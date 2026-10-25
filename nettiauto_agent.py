#!/usr/bin/env python3
"""
Nettiauto watcher: finds electric cars matching your criteria and emails
only the ones you have not been told about yet. Run it every 4 hours.

Criteria (edit below or override via env vars):
  - Electric car
  - Mileage <= 125 000 km
  - Price 14 000 - 25 000 EUR
  - Battery capacity >= 70 kWh

No third-party packages needed (Python 3.9+).
"""
import json
import os
import re
import smtplib
import ssl
import sys
import time
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from html import escape, unescape
from html.parser import HTMLParser
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qsl, urlencode, urljoin, urlparse, urlunparse
from urllib.request import Request, urlopen

# --------------------------------------------------------------------------
# Criteria
# --------------------------------------------------------------------------
MAX_MILEAGE_KM = int(os.getenv("MAX_MILEAGE_KM", 125_000))
MIN_PRICE_EUR = int(os.getenv("MIN_PRICE_EUR", 14_000))
MAX_PRICE_EUR = int(os.getenv("MAX_PRICE_EUR", 25_000))
MIN_BATTERY_KWH = float(os.getenv("MIN_BATTERY_KWH", 70))

# Where to look for candidates. Best: set your filters on nettiauto.com, then
# copy the result-page URL into the SEARCH_URL env var / secret.
# The default is the site's "Electric cars" shortcut. Every candidate's ad page
# is verified against the criteria above, so a broad URL is still safe.
SEARCH_URL = os.getenv("SEARCH_URL") or "https://www.nettiauto.com/en/pikalinkit/sahkoautot"
MAX_PAGES = int(os.getenv("MAX_PAGES", 10))
RECHECK_REJECTED_HOURS = 24  # re-check rejected ads daily (price drops etc.)

STATE_FILE = os.getenv("STATE_FILE", "state.json")
REQUEST_DELAY_S = 1.0
USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/124.0 Safari/537.36"
)

# --------------------------------------------------------------------------
# HTTP + HTML helpers
# --------------------------------------------------------------------------
def fetch(url, retries=3):
    """Return (html, final_url)."""
    last = None
    for attempt in range(retries):
        try:
            req = Request(url, headers={
                "User-Agent": USER_AGENT,
                "Accept": "text/html,application/xhtml+xml",
                "Accept-Language": "en,fi;q=0.8",
            })
            with urlopen(req, timeout=30) as r:
                charset = r.headers.get_content_charset() or "utf-8"
                return r.read().decode(charset, errors="replace"), r.geturl()
        except (HTTPError, URLError, TimeoutError) as e:
            last = e
            time.sleep(2 * (attempt + 1))
    raise RuntimeError(f"Failed to fetch {url}: {last}")


class _Text(HTMLParser):
    BLOCK = {"p", "div", "li", "br", "tr", "td", "th", "h1", "h2", "h3", "h4",
             "section", "dt", "dd", "span", "a", "ul", "table"}

    def __init__(self):
        super().__init__()
        self.parts, self._skip = [], 0

    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style", "noscript"):
            self._skip += 1
        elif tag in self.BLOCK:
            self.parts.append("\n")

    def handle_endtag(self, tag):
        if tag in ("script", "style", "noscript"):
            self._skip = max(0, self._skip - 1)
        elif tag in self.BLOCK:
            self.parts.append("\n")

    def handle_data(self, data):
        if not self._skip:
            self.parts.append(data)


def html_to_text(raw):
    p = _Text()
    p.feed(raw)
    text = unescape("".join(p.parts)).replace("\u00ad", "").replace("\xa0", " ")
    return "\n".join(l.strip() for l in text.splitlines() if l.strip())


AD_PATH = re.compile(r"^/(?:en/)?([a-z0-9-]+)/([a-z0-9-]+)/(\d{7,9})/?$")


def extract_ads(raw_html, base_url):
    """Return {ad_id: canonical_url} for every car-ad link on a results page."""
    found = {}
    for href in re.findall(r'href=["\']([^"\']+)["\']', raw_html):
        path = urlparse(urljoin(base_url, href)).path
        m = AD_PATH.match(path)
        if m:
            make, model, ad_id = m.groups()
            found[ad_id] = f"https://www.nettiauto.com/en/{make}/{model}/{ad_id}"
    return found


def with_page(url, page):
    u = urlparse(url)
    q = dict(parse_qsl(u.query))
    q["page"] = str(page)
    return urlunparse(u._replace(query=urlencode(q)))


# --------------------------------------------------------------------------
# Ad parsing + criteria check
# --------------------------------------------------------------------------
def _num(s):
    return float(s.replace(" ", "").replace(",", "."))


def _after_label(lines, labels):
    for i, l in enumerate(lines[:-1]):
        if l.lower() in labels:
            return lines[i + 1]
    return None


def parse_ad(raw_html, ad_id, url):
    text = html_to_text(raw_html)
    lines = text.splitlines()

    m = re.search(r"<h1[^>]*>(.*?)</h1>", raw_html, re.S)
    title = unescape(re.sub(r"<[^>]+>", "", m.group(1))).strip() if m else f"Ad {ad_id}"

    price = None
    m = re.search(r"(\d[\d ]*\d|\d)\s*€", text)
    if m:
        price = _num(m.group(1))

    mileage = None
    v = _after_label(lines, {"mileage", "mittarilukema"})
    if v:
        m = re.match(r"([\d ]+)\s*km", v)
        if m:
            mileage = _num(m.group(1))

    battery = None
    v = _after_label(lines, {"battery capacity", "akkukapasiteetti", "akku kapasiteetti"})
    if v:
        m = re.match(r"(\d+(?:[.,]\d+)?)\s*kwh", v, re.I)
        if m:
            battery = _num(m.group(1))
    if battery is None:  # fall back to the summary line, e.g. "64.8 kwh"
        m = re.search(r"(\d+(?:[.,]\d+)?)\s*kwh(?!\s*/)", text, re.I)
        if m:
            battery = _num(m.group(1))

    engine = _after_label(lines, {"engine", "moottori"})
    year = None
    v = _after_label(lines, {"year model", "vuosimalli"})
    if v:
        m = re.match(r"(\d{4})", v)
        year = int(m.group(1)) if m else None

    return {"id": ad_id, "url": url, "title": title, "price": price,
            "mileage": mileage, "battery": battery, "engine": engine, "year": year}


def check_criteria(ad):
    """Return None if the ad matches, else a short rejection reason."""
    if not ad["engine"] or ad["engine"].lower() not in ("electric", "sähkö"):
        return f"not electric ({ad['engine']})"
    if ad["price"] is None or not (MIN_PRICE_EUR <= ad["price"] <= MAX_PRICE_EUR):
        return f"price {ad['price']}"
    if ad["mileage"] is None or ad["mileage"] > MAX_MILEAGE_KM:
        return f"mileage {ad['mileage']}"
    if ad["battery"] is None or ad["battery"] < MIN_BATTERY_KWH:
        return f"battery {ad['battery']}"
    return None


# --------------------------------------------------------------------------
# State
# --------------------------------------------------------------------------
def load_state():
    try:
        with open(STATE_FILE, encoding="utf-8") as f:
            s = json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        s = {}
    s.setdefault("sent", {})      # ad_id -> {title, url, first_sent}
    s.setdefault("rejected", {})  # ad_id -> iso time of last check
    return s


def save_state(state):
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(state, f, indent=2, ensure_ascii=False)


# --------------------------------------------------------------------------
# Email
# --------------------------------------------------------------------------
def build_email(new_ads, first_run):
    n = len(new_ads)
    if n == 0:
        subject = "Nettiauto: no new cars"
        plain = "No new listed cars from the last 4 hours."
        html = f"<p>{plain}</p>"
        return subject, plain, html

    intro = (f"All {n} cars currently matching your criteria:" if first_run
             else f"{n} newly listed car(s) matching your criteria:")
    subject = f"Nettiauto: {n} {'matching' if first_run else 'new'} car{'s' if n != 1 else ''}"

    plain_rows, html_rows = [], []
    for a in new_ads:
        facts = (f"{a['price']:,.0f} EUR | {a['mileage']:,.0f} km | "
                 f"{a['battery']:g} kWh | {a['year'] or '?'}").replace(",", " ")
        plain_rows.append(f"- {a['title']}\n  {facts}\n  {a['url']}")
        html_rows.append(
            f"<li style='margin-bottom:12px'><a href='{escape(a['url'])}'>"
            f"<b>{escape(a['title'])}</b></a><br>{escape(facts)}</li>")
    plain = intro + "\n\n" + "\n\n".join(plain_rows)
    html = f"<p>{intro}</p><ul style='padding-left:18px'>{''.join(html_rows)}</ul>"
    return subject, plain, html


def send_email(subject, plain, html):
    host = os.environ["SMTP_HOST"]
    port = int(os.getenv("SMTP_PORT") or 465)
    user = os.environ["SMTP_USER"]
    password = os.environ["SMTP_PASSWORD"]
    to = os.environ["MAIL_TO"]

    msg = EmailMessage()
    msg["Subject"], msg["From"], msg["To"] = subject, os.getenv("MAIL_FROM", user), to
    msg.set_content(plain)
    msg.add_alternative(html, subtype="html")

    ctx = ssl.create_default_context()
    if port == 465:
        with smtplib.SMTP_SSL(host, port, context=ctx) as s:
            s.login(user, password)
            s.send_message(msg)
    else:
        with smtplib.SMTP(host, port) as s:
            s.starttls(context=ctx)
            s.login(user, password)
            s.send_message(msg)


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------
def collect_candidates():
    candidates, base = {}, SEARCH_URL
    for page in range(1, MAX_PAGES + 1):
        url = SEARCH_URL if page == 1 else with_page(base, page)
        raw, final_url = fetch(url)
        if page == 1:
            base = final_url  # shortcut URLs may redirect to the real search URL
        ads = extract_ads(raw, final_url)
        fresh = {k: v for k, v in ads.items() if k not in candidates}
        print(f"page {page}: {len(ads)} ad links, {len(fresh)} not seen before")
        if not fresh:
            break
        candidates.update(fresh)
        time.sleep(REQUEST_DELAY_S)
    return candidates


def main():
    state = load_state()
    first_run = not state["sent"]
    now = datetime.now(timezone.utc)

    candidates = collect_candidates()
    if not candidates:
        msg = ("Nettiauto agent could not find any ads on the search page. "
               "The site layout, URL or bot protection may have changed.")
        print(msg, file=sys.stderr)
        try:
            send_email("Nettiauto agent: problem", msg, f"<p>{msg}</p>")
        except Exception as e:  # noqa: BLE001
            print(f"(also failed to send alert: {e})", file=sys.stderr)
        return 1

    new_ads = []
    for ad_id, url in candidates.items():
        if ad_id in state["sent"]:
            continue
        last = state["rejected"].get(ad_id)
        if last and now - datetime.fromisoformat(last) < timedelta(hours=RECHECK_REJECTED_HOURS):
            continue
        try:
            raw, _ = fetch(url)
        except RuntimeError as e:
            print(e, file=sys.stderr)
            continue
        ad = parse_ad(raw, ad_id, url)
        reason = check_criteria(ad)
        if reason:
            state["rejected"][ad_id] = now.isoformat()
            print(f"  skip {ad_id} {ad['title']}: {reason}")
        else:
            state["rejected"].pop(ad_id, None)
            new_ads.append(ad)
            print(f"  MATCH {ad_id} {ad['title']} {ad['price']} EUR")
        time.sleep(REQUEST_DELAY_S)

    new_ads.sort(key=lambda a: a["price"])
    subject, plain, html = build_email(new_ads, first_run)
    send_email(subject, plain, html)  # raises on failure -> state is not saved

    for a in new_ads:
        state["sent"][a["id"]] = {"title": a["title"], "url": a["url"],
                                  "first_sent": now.isoformat()}
    state["rejected"] = {k: v for k, v in state["rejected"].items()
                         if now - datetime.fromisoformat(v) < timedelta(days=14)}
    save_state(state)
    print(f"Done. Emailed {len(new_ads)} car(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
