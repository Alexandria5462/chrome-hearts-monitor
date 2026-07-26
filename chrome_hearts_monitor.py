#!/usr/bin/env python3
"""
Chrome Hearts new-product monitor
=================================

Alerts you when:
  1. A brand-new product ID appears                 -> NEW ITEM
  2. A product that was sold out becomes buyable    -> RESTOCK
  3. A product page that was dead comes alive       -> WENT LIVE
  4. A whole new category opens up (e.g. /hoodie)   -> NEW CATEGORY

How it knows
------------
The site runs on Salesforce Commerce Cloud. Every product has a stable ID
baked into its web address:

    https://www.chromehearts.com/hoodie/black-hoodie/152701BLKXXX04K.html
                                                     ^^^^^^^^^^^^^^^
                                                     the product ID

So "did something new get added?" is a set difference against last run.

The redirect trick
------------------
Chrome Hearts keeps categories in their catalog long before they show them
in the site menu. /hoodie exists right now, but it is not in the nav, and its
product pages currently bounce you to the homepage.

That bounce IS the signal. A page that redirects to "/" is not live yet. The
moment it stops redirecting and returns a real page, the drop is on. This
script watches for exactly that flip.

Usage
-----
    python chrome_hearts_monitor.py --init     # first run: baseline, no alerts
    python chrome_hearts_monitor.py            # every run after: check + alert
    python chrome_hearts_monitor.py --test     # send a test notification
    python chrome_hearts_monitor.py --list     # show tracked products
    python chrome_hearts_monitor.py --status   # show category live/dead status

Requires: pip install requests
"""

import argparse
import os
import random
import re
import sqlite3
import sys
import time
import traceback
import xml.etree.ElementTree as ET
from datetime import datetime, timezone

import requests

# Some networks (corporate wifi, VPNs, antivirus with "SSL scanning") sit in
# the middle of every HTTPS connection and re-sign it with their own root
# certificate. Windows trusts that root; Python ships its own separate list
# and does not. Result: every request dies with
# "self-signed certificate in certificate chain".
#
# truststore makes Python use the Windows certificate store instead, which
# fixes it properly. Install with:  pip install truststore
try:
    import truststore
    truststore.inject_into_ssl()
    _TRUSTSTORE = True
except Exception:
    _TRUSTSTORE = False

# ===========================================================================
# SETTINGS -- the only part you need to edit
# ===========================================================================

# Put your ntfy topic between the last set of quotes. Free, no signup.
# Pick something weird; anyone who knows the topic can read your alerts.
NTFY_TOPIC = os.environ.get("NTFY_TOPIC", "alex-ch-drops-7k2m9x")

# Optional Discord channel webhook, instead of or alongside ntfy.
DISCORD_WEBHOOK = os.environ.get("DISCORD_WEBHOOK", "")

# Check whether individual products are buyable (slower but catches restocks).
CHECK_AVAILABILITY = True

# Max product pages to open per run. Keep modest so you are not hammering them.
AVAILABILITY_BUDGET = 25

# The sitemap turned out to list every category, so blind guessing is mostly
# redundant now -- and 143 guesses costs ~6 minutes per run. Keep it as an
# occasional safety net rather than a main mechanism.
PROBE_CATEGORIES_EVERY_N_RUNS = 24

# Only set this to False if you cannot install truststore and you have read
# the note in the guide. It turns off HTTPS certificate checking.
VERIFY_SSL = True

# Some category pages flip between live and empty on their own (/eyewear does
# this). Without a guard you would get a "category opened" alert every time it
# flapped back. Only alert if it has genuinely been quiet this long.
FLAP_SUPPRESS_HOURS = 12

# Seconds between requests, randomised. Do not lower these.
DELAY_MIN = 1.5
DELAY_MAX = 3.5

# ===========================================================================
# Things you probably do not need to touch
# ===========================================================================

BASE = "https://www.chromehearts.com"
DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "chrome_hearts.db")

# Salesforce Commerce Cloud serves paginated category grids from this
# endpoint. A category page only shows the first handful of products; this
# is how you get the rest without clicking "load more".
GRID_ENDPOINT = f"{BASE}/on/demandware.store/Sites-ChromeHearts-Site/default/Search-UpdateGrid"
GRID_PAGE_SIZE = 48
GRID_MAX_PAGES = 8

SITEMAP_CANDIDATES = [
    f"{BASE}/sitemap_index.xml",
    f"{BASE}/sitemap.xml",
]

# Categories confirmed to exist. Some are in the nav, some (like /hoodie) are
# not -- they live in the catalog but are hidden until a drop.
SEED_CATEGORIES = [
    # In the public nav
    "/baccarat", "/scents", "/boxers-leggings", "/intimates",
    "/socks", "/eyewear",
    # CONFIRMED REAL but hidden from the nav. Every one of these was found
    # from an actual product URL, not guessed. Most currently bounce to the
    # homepage, which means the section exists but has nothing buyable in it.
    "/hoodie", "/hat", "/shirt", "/slippers", "/gloves", "/goggles",
    "/jewelry-roll", "/rib-tank", "/after-school-flannel-shorts",
    "/boots", "/silichrome", "/love-you-crew-sweatshirt",
    # straight from the live sitemap
    "/shop", "/underwear",
]

# Slugs to probe for. Chrome Hearts uses SINGULAR slugs (/hoodie not /hoodies),
# so both forms are listed. A probe is one cheap request that answers
# "does this section exist and is it live?"
# Naming convention, learned from the confirmed slugs above:
#   - garments are SINGULAR: /shirt, /hoodie, /hat  (not /shirts)
#   - naturally-paired things stay plural: /gloves, /goggles, /slippers
#   - some are compound product names: /jewelry-roll, /rib-tank
# Both forms are listed since guessing is cheap and a miss costs one request.
CANDIDATE_CATEGORIES = [
    # tops
    "shirt", "shirts", "tshirt", "t-shirt", "tee", "tees", "top", "tops",
    "hoodie", "hoodies", "sweatshirt", "sweater", "sweaters", "crewneck",
    "long-sleeve", "short-sleeve", "tank", "rib-tank", "polo", "flannel",
    # bottoms
    "jean", "jeans", "denim", "pant", "pants", "trouser", "trousers",
    "short", "shorts", "sweatpant", "sweatpants", "legging", "leggings",
    # outerwear
    "jacket", "jackets", "coat", "coats", "outerwear", "vest", "leather",
    "fur", "puffer", "windbreaker",
    # head
    "hat", "hats", "cap", "caps", "beanie", "beanies", "headwear",
    "trucker-hat", "watch-cap", "bandana", "balaclava",
    # eyes
    "goggles", "goggle", "sunglasses", "optical", "frames",
    # hands / feet
    "gloves", "glove", "mittens", "slippers", "slipper", "footwear",
    "shoes", "shoe", "sneakers", "boots", "boot", "sandals",
    # jewelry
    "jewelry", "jewellery", "jewelry-roll", "ring", "rings", "necklace",
    "necklaces", "bracelet", "bracelets", "earring", "earrings",
    "pendant", "pendants", "chain", "chains", "cross", "silver", "gold",
    "charm", "charms", "cuff", "bangle",
    # accessories / goods
    "bag", "bags", "backpack", "wallet", "wallets", "belt", "belts",
    "scarf", "scarves", "tie", "keychain", "lighter", "pouch",
    "accessories", "accessory", "leather-goods", "luggage",
    # home
    "home", "furniture", "candle", "candles", "rug", "blanket", "towel",
    "pillow", "glassware", "tableware",
    # merchandising buckets
    "womens", "mens", "kids", "baby", "new", "new-arrivals", "collection",
    "archive", "exclusive", "exclusives", "collab", "collaboration",
    # sub-lines and collab names -- these do not follow the garment pattern
    "silichrome", "matty-boy", "mattyboy", "ch-plus", "foti", "drink-water",
    "chrome-hearts", "made-in-hollywood", "hollywood", "cemetery", "dagger",
]

# Single-segment URLs that are pages, not shop categories.
NOT_CATEGORIES = {
    "login", "cart", "contact", "account", "search", "wishlist", "checkout",
    "stores", "locations", "magazine", "terms", "privacy", "general",
    "disclosure", "returns", "shipping", "faq", "on", "s", "dw", "sitemap",
}

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
}

# Product URLs come in TWO shapes on this site:
#   /hoodie/black-hoodie/152701BLKXXX04K.html   (category / slug / id)
#   /after-school-flannel-shorts/213616AZJXXX00D.html   (slug / id)
# The {1,2} handles both. The old two-segment-only pattern silently missed
# every product of the second kind.
PRODUCT_URL_RE = re.compile(r"/(?:[a-z0-9\-]+/){1,2}([A-Z0-9\-]{6,})\.html")

# A single-segment link in the nav, e.g. /eyewear
CATEGORY_URL_RE = re.compile(
    r'href="(?:https://www\.chromehearts\.com)?/([a-z0-9\-]{2,40})"'
)

# CAREFUL: "this product is not available in your country" appears on pages
# that are perfectly in stock -- it sits right under a working Add to Bag
# button. Treating it as a sold-out signal marks every live product dead.
# It is deliberately NOT in this list.
SOLD_OUT_MARKERS = ["sold out", "out of stock", "notify me when available"]
IN_STOCK_MARKERS = ["add to bag", "add to cart"]

# Where a saved-URL watchlist lives (one URL per line, # for comments).
WATCHLIST_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                              "watchlist.txt")


if not VERIFY_SSL:
    requests.packages.urllib3.disable_warnings()


def log(msg):
    print(f"[{datetime.now():%Y-%m-%d %H:%M:%S}] {msg}", flush=True)


# ---------------------------------------------------------------------------
# Networking
# ---------------------------------------------------------------------------

def polite_pause():
    time.sleep(random.uniform(DELAY_MIN, DELAY_MAX))


def fetch(url, tries=3, timeout=25):
    """Fetch a page. Returns (text, final_url, status).

    status is one of:
      "ok"      -- got a real page
      "gone"    -- HTTP 404, the URL does not exist at all
      "failed"  -- network problem or blocked, we learned nothing

    final_url matters just as much as the text: this site redirects
    unavailable products to the homepage, so where we LANDED tells us
    whether the thing is buyable.
    """
    for attempt in range(1, tries + 1):
        try:
            resp = requests.get(url, headers=HEADERS, timeout=timeout,
                                allow_redirects=True, verify=VERIFY_SSL)
            if resp.status_code == 200:
                return resp.text, resp.url, "ok"
            if resp.status_code == 404:
                return None, None, "gone"
            if resp.status_code in (403, 429):
                wait = 10 * attempt
                log(f"  HTTP {resp.status_code} on {url}; backing off {wait}s")
                time.sleep(wait)
                continue
            log(f"  HTTP {resp.status_code} on {url}")
        except requests.exceptions.SSLError:
            log(f"  HTTPS certificate rejected on {url}")
            log("  Run:  pip install truststore   (see Part 6 of the guide)")
            return None, None, "failed"
        except requests.RequestException as exc:
            log(f"  network error on {url}: {exc}")
        time.sleep(3 * attempt)
    return None, None, "failed"


def bounced_home(final_url):
    """True if we got redirected to the homepage -- i.e. the page is not live."""
    if not final_url:
        return False
    return final_url.rstrip("/") == BASE.rstrip("/")


# ---------------------------------------------------------------------------
# Categories: which sections exist, and which are actually open
# ---------------------------------------------------------------------------

def categories_from_nav():
    """Read the site menu. Catches sections they have publicly launched."""
    found = set()
    html, _, _ = fetch(BASE + "/")
    if not html:
        log("  could not load homepage")
        return found
    for match in CATEGORY_URL_RE.finditer(html):
        slug = match.group(1)
        if slug in NOT_CATEGORIES or slug.endswith(".html"):
            continue
        found.add("/" + slug)
    return found


def products_from_grid(slug):
    """Page through a category's full product grid.

    Without this we would only ever see the first screen of each category,
    so a new item landing on page 2 would be invisible.
    """
    found = {}
    for page in range(GRID_MAX_PAGES):
        url = (f"{GRID_ENDPOINT}?cgid={slug}"
               f"&start={page * GRID_PAGE_SIZE}&sz={GRID_PAGE_SIZE}")
        html, final, status = fetch(url, tries=1)
        if status != "ok" or not html or bounced_home(final):
            break
        before = len(found)
        for match in PRODUCT_URL_RE.finditer(html):
            found.setdefault(match.group(1),
                             {"url": BASE + match.group(0), "lastmod": ""})
        if len(found) == before:
            break          # nothing new on this page, we have reached the end
        polite_pause()
    return found


def probe_category(path):
    """Ask one category URL what state it is in.

    Returns (state, products) where state is:
      "live"     -- has buyable products
      "empty"    -- real section, but bounces to the homepage
      "unknown"  -- request failed; we learned NOTHING and must not guess

    The "unknown" case matters. Treating a failed request as "empty" meant a
    single network blip marked a live category dead, and the next successful
    run then fired a bogus "category opened" alert.
    """
    html, final, status = fetch(BASE + path, tries=2)
    if status == "failed":
        return "unknown", {}
    if status == "gone" or html is None:
        return "empty", {}
    if bounced_home(final):
        return "empty", {}

    products = {}
    for match in PRODUCT_URL_RE.finditer(html):
        products[match.group(1)] = {"url": BASE + match.group(0), "lastmod": ""}

    # The landing page shows only the first batch. Ask for the rest.
    deeper = products_from_grid(path.strip("/"))
    if deeper:
        added = len(set(deeper) - set(products))
        if added:
            log(f"    {path}: +{added} more from paged grid")
        products.update(deeper)

    return "live", products


# ---------------------------------------------------------------------------
# Products
# ---------------------------------------------------------------------------

def harvest_sitemap():
    """Read the sitemap. Returns (categories, products).

    IMPORTANT, learned from the live site: Chrome Hearts' sitemap does NOT
    list products. It lists CATEGORY pages -- /shop, /eyewear, /hat,
    /underwear and so on. That makes it useless for finding new items, but it
    makes it the single best source for finding new SECTIONS, including ones
    hidden from the nav that no wordlist would ever guess.

    So we mine it for categories, and take any product URLs as a bonus.
    """
    cats, products = set(), {}
    ns = {"sm": "http://www.sitemaps.org/schemas/sitemap/0.9"}

    def absorb(root):
        for loc_el in root.findall(".//sm:url/sm:loc", ns):
            if not loc_el.text:
                continue
            loc = loc_el.text.strip()
            match = PRODUCT_URL_RE.search(loc)
            if match:
                products[match.group(1)] = {"url": loc, "lastmod": ""}
                cat = category_of(loc)
                if cat:
                    cats.add(cat)
                continue
            path = loc.replace(BASE, "").split("?")[0]
            parts = [x for x in path.split("/") if x]
            if (len(parts) == 1 and not parts[0].endswith(".html")
                    and parts[0] not in NOT_CATEGORIES):
                cats.add("/" + parts[0])

    for candidate in SITEMAP_CANDIDATES:
        raw, _, status = fetch(candidate, tries=2)
        if not raw:
            continue
        log(f"  sitemap found: {candidate}")
        try:
            root = ET.fromstring(raw.encode("utf-8"))
        except ET.ParseError:
            log("  sitemap was not valid XML, skipping")
            continue

        children = [e.text.strip() for e in root.findall(".//sm:sitemap/sm:loc", ns) if e.text]
        if children:
            log(f"  index with {len(children)} child sitemap(s)")
            for child in children:
                polite_pause()
                craw, _, cstatus = fetch(child, tries=2)
                if not craw:
                    log(f"  child sitemap unreadable ({cstatus})")
                    continue
                try:
                    absorb(ET.fromstring(craw.encode("utf-8")))
                except ET.ParseError:
                    log("  child sitemap was not valid XML")
        else:
            absorb(root)

        if cats or products:
            break

    log(f"  sitemap gave {len(cats)} categories, {len(products)} products")
    return cats, products


def _extract_locs(root, ns):
    out = {}
    for url_el in root.findall(".//sm:url", ns):
        loc_el = url_el.find("sm:loc", ns)
        if loc_el is None or not loc_el.text:
            continue
        loc = loc_el.text.strip()
        match = PRODUCT_URL_RE.search(loc)
        if not match:
            continue
        mod_el = url_el.find("sm:lastmod", ns)
        out[match.group(1)] = {
            "url": loc,
            "lastmod": mod_el.text.strip() if mod_el is not None and mod_el.text else "",
        }
    return out


def product_state(url):
    """What state is this product in? Verified against real URLs.

    Returns one of:
      "available"    -- page loads, Add to Bag present. You can buy it.
      "unavailable"  -- page bounces to the homepage. Sold out / pulled.
      "gone"         -- HTTP 404. Never existed, or fully removed.
      None           -- could not tell (network trouble)

    The homepage bounce is the key signal on this site. Confirmed:
    the black hoodie, the baby blue rib tank and the flannel shorts all
    bounce; the Hollyweird frames, CH logo socks and classic rib boxer
    brief all load normally.
    """
    html, final, status = fetch(url, tries=2)
    if status == "gone":
        return "gone"
    if status == "failed" or html is None:
        return None
    if bounced_home(final):
        return "unavailable"
    low = html.lower()
    if any(m in low for m in SOLD_OUT_MARKERS):
        return "unavailable"
    if any(m in low for m in IN_STOCK_MARKERS):
        return "available"
    return None


def category_of(url):
    """The category segment of a product URL.

    /silichrome/crossball-charm/218675H1UXXXOON.html  -> /silichrome
    /love-you-crew-sweatshirt/196533WHTXXX01Z.html    -> /love-you-crew-sweatshirt
    """
    path = url.replace(BASE, "").split("?")[0]
    parts = [x for x in path.split("/") if x]
    if not parts:
        return None
    slug = parts[0]
    if slug in NOT_CATEGORIES or slug.endswith(".html"):
        return None
    return "/" + slug


def learn_categories(conn, products, known_cats):
    """Discover categories from the product URLs we already found.

    This beats guessing. Slugs like /silichrome (a sub-line) and
    /love-you-crew-sweatshirt (a product name used as a category) were never
    going to appear in any wordlist -- but the moment one of their products
    shows up anywhere, the category reveals itself.

    Finding a product inside a section PROVES that section is live, so this
    also upgrades sections we had previously probed and written off as empty.
    That upgrade is the whole point: a category sitting dead for weeks and
    then yielding a product is exactly what a drop looks like.
    """
    found = []
    for info in products.values():
        cat = category_of(info["url"])
        if cat and cat not in found:
            found.append(cat)

    newly_live = []
    for cat in found:
        was_live = known_cats.get(cat)          # True / False / None(never seen)
        if was_live is not True:
            newly_live.append((cat, was_live is None))
        conn.execute("""
            INSERT INTO categories
                (path, live, confirmed, first_seen, went_live, last_probed)
            VALUES (?, 1, 1, ?, ?, ?)
            ON CONFLICT(path) DO UPDATE SET
                live = 1,
                confirmed = 1,
                went_live = COALESCE(categories.went_live, excluded.went_live),
                last_probed = excluded.last_probed
        """, (cat, now_iso(), now_iso(), now_iso()))
    return newly_live


def slug_key(url):
    """The product's identity, ignoring size/colour variant IDs.

    /socks/ch-logo-socks/176354XXXXXX349.html  and
    /socks/ch-logo-socks/176354BLKSML349.html  are the SAME product --
    the second is just the black/small variant. Both reduce to
    /socks/ch-logo-socks, so we never alert twice for one item.
    """
    path = url.replace(BASE, "").split("?")[0]
    return path.rsplit("/", 1)[0]


def load_watchlist():
    """Specific URLs you care about, checked every run no matter what."""
    if not os.path.exists(WATCHLIST_PATH):
        log("  NOTE: watchlist.txt not found next to the script -- watchlist")
        log("        alerts are OFF. Put watchlist.txt in the same folder.")
        return []
    urls = []
    # utf-8-sig strips the invisible byte-order mark Notepad adds on Windows.
    # Without it the first URL in the file silently breaks.
    with open(WATCHLIST_PATH, encoding="utf-8-sig") as fh:
        for line in fh:
            line = line.strip()
            if line and not line.startswith("#"):
                if not line.startswith("http"):
                    log(f"  skipping unusable watchlist line: {line[:60]}")
                    continue
                urls.append(line)
    return urls


def pretty_name(url):
    """Readable label. Handles both URL shapes without echoing the raw ID."""
    parts = [x for x in url.replace(BASE, "").split("?")[0].split("/") if x]
    parts = [x for x in parts if not x.endswith(".html")]
    if len(parts) >= 2:
        return f"{parts[0].replace('-', ' ').title()} - {parts[1].replace('-', ' ').title()}"
    if len(parts) == 1:
        return parts[0].replace("-", " ").title()
    return url


# ---------------------------------------------------------------------------
# Saved state
# ---------------------------------------------------------------------------

def db_connect():
    conn = sqlite3.connect(DB_PATH)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS products (
            pid TEXT PRIMARY KEY, url TEXT, name TEXT, state TEXT,
            lastmod TEXT, first_seen TEXT, last_seen TEXT, last_checked TEXT
        )""")
    conn.execute("""
        CREATE TABLE IF NOT EXISTS categories (
            path TEXT PRIMARY KEY, live INTEGER, confirmed INTEGER,
            first_seen TEXT, went_live TEXT, last_probed TEXT, last_live TEXT
        )""")
    conn.execute("CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT)")
    # migrate older databases in place
    cols = {r[1] for r in conn.execute("PRAGMA table_info(categories)")}
    if "last_live" not in cols:
        conn.execute("ALTER TABLE categories ADD COLUMN last_live TEXT")
    conn.commit()
    return conn


def meta_get(conn, key, default="0"):
    row = conn.execute("SELECT value FROM meta WHERE key = ?", (key,)).fetchone()
    return row[0] if row else default


def meta_set(conn, key, value):
    conn.execute(
        "INSERT INTO meta (key, value) VALUES (?, ?) "
        "ON CONFLICT(key) DO UPDATE SET value = excluded.value",
        (key, str(value)))


def now_iso():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def load_products(conn):
    rows = conn.execute(
        "SELECT pid, url, state, last_checked FROM products").fetchall()
    return {pid: {"url": u, "state": s, "last_checked": lc or ""}
            for pid, u, s, lc in rows}


def load_categories(conn):
    rows = conn.execute("SELECT path, live FROM categories").fetchall()
    return {path: bool(live) for path, live in rows}


def load_real_categories(conn):
    """Only sections we have evidence are real -- seen live, or proven by a
    product URL. The ~124 slugs we merely guessed at and found nothing for do
    not deserve a request every single run."""
    rows = conn.execute(
        "SELECT path FROM categories WHERE confirmed = 1 OR live = 1").fetchall()
    return {r[0] for r in rows}


def save_product(conn, pid, url, lastmod, state, checked):
    conn.execute("""
        INSERT INTO products
            (pid, url, name, state, lastmod, first_seen, last_seen, last_checked)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(pid) DO UPDATE SET
            url = excluded.url,
            lastmod = excluded.lastmod,
            state = COALESCE(excluded.state, products.state),
            last_seen = excluded.last_seen,
            last_checked = COALESCE(excluded.last_checked, products.last_checked)
    """, (pid, url, pretty_name(url), state, lastmod,
          now_iso(), now_iso(), now_iso() if checked else None))


def hours_since(iso_ts):
    if not iso_ts:
        return None
    try:
        then = datetime.fromisoformat(iso_ts)
    except ValueError:
        return None
    if then.tzinfo is None:
        then = then.replace(tzinfo=timezone.utc)
    return (datetime.now(timezone.utc) - then).total_seconds() / 3600.0


def save_category(conn, path, live):
    """confirmed = we know this section is real, either because a real product
    URL proved it or because we have seen it live. Everything else is just a
    slug we guessed at, and is kept quiet."""
    ts = now_iso()
    confirmed = 1 if (live or path in SEED_CATEGORIES) else 0
    conn.execute("""
        INSERT INTO categories
            (path, live, confirmed, first_seen, went_live, last_probed, last_live)
        VALUES (?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(path) DO UPDATE SET
            live = excluded.live,
            confirmed = MAX(categories.confirmed, excluded.confirmed),
            went_live = CASE WHEN excluded.live = 1 AND categories.went_live IS NULL
                             THEN excluded.last_probed ELSE categories.went_live END,
            last_probed = excluded.last_probed,
            last_live = COALESCE(excluded.last_live, categories.last_live)
    """, (path, 1 if live else 0, confirmed, ts, ts if live else None, ts,
          ts if live else None))


# ---------------------------------------------------------------------------
# Notifications
# ---------------------------------------------------------------------------

def notify(title, body, url=None):
    sent = False
    if NTFY_TOPIC:
        try:
            headers = {"Title": title, "Priority": "high", "Tags": "gem"}
            if url:
                headers["Click"] = url
            requests.post(f"https://ntfy.sh/{NTFY_TOPIC}",
                          data=body.encode("utf-8"), headers=headers,
                          timeout=15, verify=VERIFY_SSL)
            sent = True
        except requests.exceptions.SSLError:
            log("  ntfy failed: HTTPS certificate rejected.")
            log("  Your network is intercepting HTTPS. Fix it with:")
            log("      pip install truststore")
            log("  then run this again. See Part 6 of the guide.")
        except requests.RequestException as exc:
            log(f"  ntfy failed: {exc}")
    if DISCORD_WEBHOOK:
        try:
            requests.post(DISCORD_WEBHOOK,
                          json={"content": f"**{title}**\n{body}"},
                          timeout=15, verify=VERIFY_SSL)
            sent = True
        except requests.RequestException as exc:
            log(f"  discord failed: {exc}")
    if not sent:
        log(f"NOTIFY (no channel configured): {title} | {body}")


# ---------------------------------------------------------------------------
# Main run
# ---------------------------------------------------------------------------

def run(init=False):
    conn = db_connect()
    known_products = load_products(conn)
    known_cats = load_categories(conn)

    try:
        run_count = int(meta_get(conn, "run_count")) + 1
    except (TypeError, ValueError):
        run_count = 1
    meta_set(conn, "run_count", run_count)

    log(f"Run #{run_count} | tracking {len(known_products)} products, "
        f"{len(known_cats)} categories")

    # --- 1. Which categories exist, and are they open? --------------------
    log("Reading sitemap for category list...")
    sitemap_cats, sitemap_products = harvest_sitemap()

    log("Checking categories...")
    to_probe = (set(SEED_CATEGORIES) | categories_from_nav()
                | load_real_categories(conn) | sitemap_cats)

    do_full_probe = init or (run_count % PROBE_CATEGORIES_EVERY_N_RUNS == 0)
    if do_full_probe:
        log(f"  full probe: also testing {len(CANDIDATE_CATEGORIES)} candidate "
            f"slugs and every section seen before (slow, ~6 min)")
        to_probe |= {"/" + s for s in CANDIDATE_CATEGORIES} | set(known_cats)
    else:
        log(f"  probing {len(to_probe)} known-real sections "
            f"(full sweep every {PROBE_CATEGORIES_EVERY_N_RUNS} runs)")

    live_cats, cat_products = [], {}
    new_cats, opened_cats = [], []

    unknown_cats = 0
    for path in sorted(to_probe):
        polite_pause()
        state, products = probe_category(path)

        if state == "unknown":
            # Learned nothing. Leave whatever we already knew untouched.
            unknown_cats += 1
            continue

        is_live = state == "live"
        if is_live:
            live_cats.append(path)
            cat_products.update(products)

        was_known = path in known_cats
        if is_live and not was_known and not init:
            new_cats.append(path)
        elif is_live and was_known and not known_cats[path] and not init:
            # Was it live very recently? Then this is flapping, not a launch.
            row = conn.execute(
                "SELECT last_live FROM categories WHERE path = ?", (path,)).fetchone()
            age = hours_since(row[0]) if row else None
            if age is not None and age < FLAP_SUPPRESS_HOURS:
                log(f"  {path} flapped back (live {age:.1f}h ago) -- not alerting")
            else:
                opened_cats.append(path)

        # Save every category we actually got an answer for. The empty ones
        # are the interesting list -- that is the staging area to watch.
        save_category(conn, path, is_live)

    conn.commit()
    log(f"  {len(live_cats)} live: {', '.join(live_cats) if live_cats else 'none'}")
    if unknown_cats:
        log(f"  {unknown_cats} could not be reached this run (left unchanged)")

    for path in new_cats:
        log(f"  NEW CATEGORY: {path}")
        notify("New Chrome Hearts category",
               f"A new section is live: {path}\n{BASE}{path}", url=BASE + path)
    for path in opened_cats:
        log(f"  CATEGORY OPENED: {path}")
        notify("Chrome Hearts category opened",
               f"{path} just went live\n{BASE}{path}", url=BASE + path)

    # --- 2. Collect products ----------------------------------------------
    log("Collecting products...")
    products = dict(sitemap_products)
    if products:
        log(f"  {len(products)} from sitemap")
    for pid, info in cat_products.items():
        products.setdefault(pid, info)
    log(f"  {len(products)} products total")

    if not products:
        log("Found nothing. Site may be blocking us, or the layout changed.")
        conn.close()
        return 1

    # Any product URL reveals its own category. Learn from that instead of
    # relying on the guess list.
    cat_state = dict(known_cats)
    for c in live_cats:
        cat_state[c] = True
    learned = learn_categories(conn, products, cat_state)
    if learned:
        conn.commit()
        log(f"  proved live from product URLs: "
            f"{', '.join(c for c, _ in learned)}")
        if not init:
            for cat, never_seen in learned:
                if never_seen:
                    notify("New Chrome Hearts category",
                           f"Found a section we had never seen: {cat}\n{BASE}{cat}",
                           url=BASE + cat)
                else:
                    notify("Chrome Hearts category opened",
                           f"{cat} was empty and now has stock\n{BASE}{cat}",
                           url=BASE + cat)

    known_slugs = {slug_key(v["url"]) for v in known_products.values()}
    states_seed = {}
    new_ids = []
    for pid in products:
        if pid in known_products:
            continue
        # A variant ID of something we already know is not a new product.
        if slug_key(products[pid]["url"]) in known_slugs:
            continue
        new_ids.append(pid)
    existing = [p for p in products if p in known_products]
    log(f"  {len(new_ids)} new product IDs")

    # --- 3. Watchlist: specific URLs you asked to be told about ------------
    watch = load_watchlist()
    if watch:
        log(f"Checking watchlist ({len(watch)} URLs)"
            f"{' -- baseline only, no alerts' if init else ''}...")
        for url in watch:
            polite_pause()
            state = product_state(url)
            pid_match = PRODUCT_URL_RE.search(url)
            pid = pid_match.group(1) if pid_match else url
            was = known_products.get(pid, {}).get("state")
            log(f"  watch {pid}: {was or 'new'} -> {state}")
            if state == "available" and was != "available" and not init:
                notify("WATCHLIST: it is up",
                       f"{pretty_name(url)}\nAvailable now\n{url}", url=url)
            if pid in products:
                states_seed[pid] = state
            else:
                products[pid] = {"url": url, "lastmod": ""}
                states_seed[pid] = state

    # --- 4. Check product states ------------------------------------------
    # Priority: new items, then things that were dead or sold out (those are
    # the ones that flip), then whatever is most stale.
    to_check = []
    if CHECK_AVAILABILITY and not init:
        to_check = [p for p in new_ids if p not in states_seed][:AVAILABILITY_BUDGET]
        left = AVAILABILITY_BUDGET - len(to_check)
        if left > 0:
            flippable = [p for p in existing
                         if known_products[p]["state"] in ("unavailable", "gone")]
            random.shuffle(flippable)
            to_check += flippable[:left]
            left -= len(flippable[:left])
        if left > 0:
            seen = set(to_check)
            stale = sorted((p for p in existing if p not in seen),
                           key=lambda p: known_products[p]["last_checked"])
            to_check += stale[:left]

    states = dict(states_seed)
    for i, pid in enumerate(to_check, 1):
        polite_pause()
        states[pid] = product_state(products[pid]["url"])
        if i % 10 == 0:
            log(f"  checked {i}/{len(to_check)}")

    # Things that flipped from dead/sold-out into buyable
    went_live = [p for p in existing
                 if known_products[p]["state"] in ("unavailable", "gone")
                 and states.get(p) == "available"]

    checked = set(to_check) | set(states_seed)
    for pid, info in products.items():
        save_product(conn, pid, info["url"], info["lastmod"],
                     states.get(pid), pid in checked and states.get(pid) is not None)
    conn.commit()

    if init:
        log(f"Baseline saved: {len(products)} products, {len(live_cats)} live "
            f"categories. No alerts sent.")
        conn.close()
        return 0

    # --- 5. Alerts ---------------------------------------------------------
    labels = {"available": "AVAILABLE NOW", "unavailable": "sold out",
              "gone": "page removed", None: "status unknown"}

    for pid in new_ids:
        info = products[pid]
        tag = labels.get(states.get(pid), "status unknown")
        notify("New Chrome Hearts item",
               f"{pretty_name(info['url'])}\n{tag}\n{info['url']}", url=info["url"])
        log(f"  NEW: {pid} {pretty_name(info['url'])} ({tag})")

    for pid in went_live:
        info = products[pid]
        notify("Chrome Hearts item is live",
               f"{pretty_name(info['url'])}\nNow buyable\n{info['url']}",
               url=info["url"])
        log(f"  LIVE: {pid} {pretty_name(info['url'])}")

    if not (new_ids or went_live or new_cats or opened_cats):
        log("No changes.")

    conn.close()
    return 0


def list_tracked():
    conn = db_connect()
    rows = conn.execute(
        "SELECT pid, name, state, first_seen FROM products ORDER BY first_seen DESC"
    ).fetchall()
    if not rows:
        print("Nothing tracked yet. Run with --init first.")
        return
    print(f"{len(rows)} products tracked\n")
    for pid, name, state, first_seen in rows:
        print(f"{first_seen[:10]}  {pid:<20} {(state or 'unknown'):<12} {name}")
    conn.close()


def debug_sitemap():
    """Find out WHY the sitemap yielded nothing. Prints raw detail."""
    print("\n=== SITEMAP DIAGNOSTIC ===\n")
    for candidate in SITEMAP_CANDIDATES:
        print(f"Fetching {candidate}")
        raw, final, status = fetch(candidate, tries=2)
        print(f"  status={status}  landed={final}")
        if not raw:
            print("  -> nothing returned\n")
            continue
        print(f"  length={len(raw)} chars")
        print(f"  starts with: {raw[:120]!r}")
        if raw.lstrip().startswith("\x1f\x8b") or raw[:2] == "\x1f\x8b":
            print("  -> looks GZIPPED, that would explain a parse failure")
        try:
            root = ET.fromstring(raw.encode("utf-8"))
        except ET.ParseError as exc:
            print(f"  -> XML PARSE FAILED: {exc}\n")
            continue
        ns = {"sm": "http://www.sitemaps.org/schemas/sitemap/0.9"}
        children = [e.text.strip() for e in root.findall(".//sm:sitemap/sm:loc", ns) if e.text]
        urls = [e.text.strip() for e in root.findall(".//sm:url/sm:loc", ns) if e.text]
        print(f"  child sitemaps: {len(children)}   direct urls: {len(urls)}")
        print(f"  root tag: {root.tag}")

        for child in children:
            print(f"\n  -- child: {child}")
            praw, pfinal, pstatus = fetch(child, tries=2)
            print(f"     status={pstatus}  landed={pfinal}")
            if not praw:
                print("     -> nothing returned")
                continue
            print(f"     length={len(praw)} chars")
            print(f"     starts with: {praw[:150]!r}")
            try:
                croot = ET.fromstring(praw.encode("utf-8"))
            except ET.ParseError as exc:
                print(f"     -> XML PARSE FAILED: {exc}")
                continue
            clocs = [e.text.strip() for e in croot.findall(".//sm:url/sm:loc", ns) if e.text]
            print(f"     <url> entries: {len(clocs)}")
            matched = [u for u in clocs if PRODUCT_URL_RE.search(u)]
            print(f"     matching the product pattern: {len(matched)}")
            print("     first 8 URLs found:")
            for u in clocs[:8]:
                print(f"       {u}")
        print()

    print("=== GRID ENDPOINT DIAGNOSTIC ===\n")
    for slug in ["eyewear", "socks"]:
        url = f"{GRID_ENDPOINT}?cgid={slug}&start=0&sz=48"
        print(f"Fetching {url}")
        raw, final, status = fetch(url, tries=1)
        print(f"  status={status}  landed={final}")
        if raw:
            hits = len(set(m.group(1) for m in PRODUCT_URL_RE.finditer(raw)))
            print(f"  length={len(raw)}  distinct product IDs found={hits}")
        print()


def show_status(show_all=False):
    conn = db_connect()
    rows = conn.execute(
        "SELECT path, live, confirmed, went_live FROM categories "
        "ORDER BY live DESC, path").fetchall()
    if not rows:
        print("No categories tracked yet. Run with --init first.")
        return

    live = [r for r in rows if r[1]]
    staged = [r for r in rows if not r[1] and r[2]]
    guesses = [r for r in rows if not r[1] and not r[2]]

    print(f"\nOPEN NOW ({len(live)})")
    for path, _, _, went_live in live:
        extra = f"   first seen live {went_live[:10]}" if went_live else ""
        print(f"   {path}{extra}")

    print(f"\nREAL BUT EMPTY ({len(staged)})   <- the watch list")
    print("   These sections exist and bounce to the homepage. When one")
    print("   stops bouncing, that is a drop.")
    for path, _, _, _ in staged:
        print(f"   {path}")

    if show_all:
        print(f"\nGUESSED SLUGS, NEVER SEEN LIVE ({len(guesses)})")
        for path, _, _, _ in guesses:
            print(f"   {path}")
    else:
        print(f"\n(+ {len(guesses)} guessed slugs probed, none live. "
              f"--status-all to list them.)")
    conn.close()


def main():
    parser = argparse.ArgumentParser(description="Chrome Hearts monitor")
    parser.add_argument("--init", action="store_true",
                        help="First run: save a baseline without alerts")
    parser.add_argument("--test", action="store_true",
                        help="Send a test notification")
    parser.add_argument("--list", action="store_true",
                        help="Show tracked products")
    parser.add_argument("--status", action="store_true",
                        help="Show which categories are open vs empty")
    parser.add_argument("--status-all", action="store_true",
                        help="Same, including every guessed slug")
    parser.add_argument("--debug-sitemap", action="store_true",
                        help="Diagnose why the sitemap is not yielding products")
    args = parser.parse_args()

    if args.test:
        log(f"Windows certificate store in use: {'YES' if _TRUSTSTORE else 'NO'}"
            f"{'' if _TRUSTSTORE else '  <- run: pip install truststore'}")
        log(f"HTTPS verification: {'on' if VERIFY_SSL else 'OFF'}")
        log(f"ntfy topic: {NTFY_TOPIC or '(not set)'}")
        notify("Test alert", "If you can read this, notifications work.",
               url=BASE)
        log("Test notification sent.")
        return 0
    if getattr(args, "debug_sitemap", False):
        debug_sitemap()
        return 0
    if args.list:
        list_tracked()
        return 0
    if args.status or getattr(args, "status_all", False):
        show_status(show_all=getattr(args, "status_all", False))
        return 0

    # If this crashes on a schedule you would never find out, because nobody
    # reads scheduler logs. Send the failure to your phone instead.
    try:
        return run(init=args.init)
    except KeyboardInterrupt:
        log("Stopped by user.")
        return 1
    except Exception as exc:
        log(f"CRASHED: {type(exc).__name__}: {exc}")
        traceback.print_exc()
        try:
            notify("Chrome Hearts monitor crashed",
                   f"{type(exc).__name__}: {exc}\n"
                   f"It will retry on the next scheduled run.")
        except Exception:
            pass
        return 1


if __name__ == "__main__":
    sys.exit(main())
