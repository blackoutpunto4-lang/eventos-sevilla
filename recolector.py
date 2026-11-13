#!/usr/bin/env python3
"""
recolector.py  -  Recoge charlas universitarias y torneos de ajedrez de Sevilla y genera eventos.json

Charlas: Eventos UPO (ICS), Eventos US (RSS), DivulgaUS, IBiS, Facultad de Física y Fundación Cajasol.
Laureados: lista oficial de los Nobel (se actualiza sola) + laureados.json (Fields, Turing, Abel).
Prensa: pistas de visitas de laureados en Google Noticias.
Torneos: Delegación Sevillana de Ajedrez + calendario FADA (lee las bases en PDF).
Recomendado:  pip install truststore pypdf

Uso (en PowerShell, dentro de la carpeta eventos-sevilla):
    python recolector.py                 -> genera eventos.json
    python recolector.py --descartados   -> además lista lo que se ha descartado y por qué
    python recolector.py --laureados     -> además fuerza la actualización de la lista de Nobel
    python recolector.py --prueba        -> comprueba que los filtros funcionan (sin internet)
"""
import argparse
import hashlib
import html
import io
import json
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from urllib.parse import quote_plus, urljoin

# Usa los certificados de Windows (evita el error CERTIFICATE_VERIFY_FAILED en algunos PC).
# Es opcional: si no está instalado, Python usa sus certificados normales.
try:
    import truststore
    truststore.inject_into_ssl()
except ImportError:
    pass

# Para leer las bases en PDF de los torneos (pip install pypdf). Opcional.
try:
    from pypdf import PdfReader
except ImportError:
    PdfReader = None

CARPETA = Path(__file__).resolve().parent
SALIDA = CARPETA / "eventos.json"
ARCHIVO_LAUREADOS = CARPETA / "laureados.json"
USER_AGENT = "Mozilla/5.0 (compatible; EventosSevilla/1.0)"

FUENTES = [
    # (código, tipo de lector, nombre para mostrar, url)
    ("upo", "ics", "Universidad Pablo de Olavide", "https://eventos.upo.es/ics/location/espana/lo-1.ics"),
    ("us", "rss", "Universidad de Sevilla", "https://eventos.us.es/rss/campus/557/all/principal.rss"),
]

# ----------------------------------------------------------------------------
# Reglas de filtrado (todo se compara sin acentos y en minúsculas)
# ----------------------------------------------------------------------------
# Palabras que indican que el evento es una charla
PALABRAS_CHARLA = re.compile(
    r"\b(charla|conferencia|ponencia|seminario|coloquio|leccion|lectio|mesa redonda|"
    r"conversatorio|conversacion|encuentro con|dialogo|cafe con ciencia|ciencia en el bar|divulgacion|"
    r"ciclo de conferencias|ciclo de charlas|lecture|talk|colloquium|keynote)"
)
# En la descripción solo se buscan palabras que dejan claro que es una charla
CHARLA_FUERTE = re.compile(
    r"\b(charla|conferencia|ponencia|seminario|coloquio|leccion|lectio|mesa redonda|conversatorio|"
    r"ciclo de conferencias|ciclo de charlas|lecture|colloquium|keynote)"
)
# Palabras que descartan un evento aunque parezca charla
PALABRAS_EXCLUIR = re.compile(
    r"\b(mercado|donacion|sangre|olimpiada|cine|proyeccion|certamen|festival|bienvenida|"
    r"premios? a la excelencia|curso|course|matricula|presentacion del libro|flamenco|concierto|exposicion|"
    r"taller|escape room|teatro|visita guiada|visitas|musical|espectaculo|magia|cuentacuentos|"
    r"puertas abiertas|congreso|workshop|consortium|hackathon|feria|jornada formativa)"
)
# 'inicio de curso', 'curso académico'... no son cursos de verdad
FRASES_CURSO = re.compile(r"(?:inicio|apertura|inauguracion|comienzo|fin|clausura)\s+del?\s+curso(?:\s+academico)?|"
                          r"curso\s+academico|curso\s+20\d\d")
# Menciones suaves a un premio de nivel Nobel
MENCION_PREMIO = re.compile(
    r"\b(nobel|medalla fields|fields medal|premio turing|turing award|premio abel|abel prize)\b"
)
# Para nombres muy comunes: solo cuentan si el texto también habla de un premio
CONTEXTO_PREMIO = re.compile(r"\b(nobel|fields|turing|abel|laureado|laureada|laureate)\b")

# Si el lugar menciona una de estas ciudades (y no menciona Sevilla), se descarta
OTRAS_CIUDADES = re.compile(
    r"\b(jerez|cadiz|malaga|granada|cordoba|huelva|almeria|jaen|madrid|barcelona|valencia|"
    r"bilbao|zaragoza|salamanca|merida|badajoz|murcia|valladolid|santander|oviedo|vigo|"
    r"la coruna|alicante|toledo|pamplona|san sebastian|london|paris|berlin)\b"
)


def normalizar(texto):
    """Minúsculas, sin acentos, sin entidades HTML y con comillas normales."""
    texto = html.unescape(texto or "")
    texto = texto.replace("’", "'").replace("‘", "'")
    texto = unicodedata.normalize("NFD", texto)
    texto = "".join(c for c in texto if unicodedata.category(c) != "Mn")
    return texto.lower()


# ----------------------------------------------------------------------------
# Hora de Madrid sin depender de bases de datos de zonas horarias
# ----------------------------------------------------------------------------
def _ultimo_domingo(anio, mes):
    d = datetime(anio, mes, 31, 1, 0, tzinfo=timezone.utc)  # marzo y octubre tienen 31 días
    while d.weekday() != 6:
        d -= timedelta(days=1)
    return d


def utc_a_madrid(dt_utc):
    """Convierte una hora UTC (con tzinfo) en hora local de Madrid (sin tzinfo)."""
    inicio = _ultimo_domingo(dt_utc.year, 3)
    fin = _ultimo_domingo(dt_utc.year, 10)
    horas = 2 if inicio <= dt_utc < fin else 1
    return (dt_utc + timedelta(hours=horas)).replace(tzinfo=None)


def hoy_madrid():
    return utc_a_madrid(datetime.now(timezone.utc)).date()


# ----------------------------------------------------------------------------
# Laureados
# ----------------------------------------------------------------------------
ARCHIVO_NOBEL = CARPETA / "laureados_nobel.json"   # copia de la lista oficial de los Nobel (se renueva sola)
DIAS_RENOVAR_NOBEL = 7

# Para marcar como "nombre común" (y exigir contexto de premio) a los laureados que baja la API:
# solo si el nombre Y el apellido son muy corrientes (p. ej. "John Clarke", "David Baker").
NOMBRES_COMUNES = {
    "john", "james", "michael", "david", "robert", "william", "richard", "peter", "paul", "thomas",
    "charles", "george", "joseph", "daniel", "mark", "steven", "stephen", "brian", "kevin", "eric",
    "jack", "jeffrey", "andrew", "anthony", "edward", "frank", "gary", "gregory", "harold", "henry",
    "kenneth", "larry", "martin", "patrick", "philip", "raymond", "roger", "ronald", "samuel", "scott",
    "simon", "stanley", "timothy", "tom", "walter", "jennifer", "elizabeth", "susan", "linda",
    "barbara", "carol", "donna", "mary", "anne", "maria", "ana", "jose", "juan", "carlos", "luis",
    "manuel", "antonio", "francisco", "miguel", "pedro", "jesus", "angel",
}
APELLIDOS_COMUNES = {
    "smith", "johnson", "brown", "clark", "clarke", "martin", "young", "hall", "wilson", "robinson",
    "roberts", "lee", "king", "wright", "scott", "green", "baker", "adams", "nelson", "hill",
    "campbell", "mitchell", "carter", "turner", "phillips", "parker", "evans", "edwards", "collins",
    "stewart", "morris", "rogers", "cook", "morgan", "bell", "murphy", "bailey", "cooper", "cox",
    "howard", "ward", "gray", "james", "watson", "kelly", "price", "bennett", "wood", "ross",
    "henderson", "perry", "powell", "long", "hughes", "foster", "ford", "hamilton", "graham",
    "wallace", "west", "cole", "jordan", "fisher", "ellis", "harrison", "gibson", "marshall",
    "harris", "thompson", "white", "lewis", "walker", "allen", "kim", "chen", "wang", "zhang",
    "liu", "yang", "taylor", "moore", "jackson", "martinez", "garcia", "lopez", "gonzalez",
    "rodriguez", "fernandez", "sanchez", "perez", "gomez", "diaz", "ruiz", "alvarez", "romero",
}
CATEGORIAS_NOBEL = {"Physics": "Física", "Chemistry": "Química",
                    "Physiology or Medicine": "Medicina", "Economic Sciences": "Economía"}
CODIGOS_NOBEL = ["phy", "che", "med", "eco"]


def _sin_iniciales(nombre):
    """'Michel H. Devoret' -> 'Michel Devoret'."""
    return " ".join(p for p in nombre.split() if not re.fullmatch(r"[A-Za-z]\.?", p))


def actualizar_laureados_nobel(forzar=False):
    """Descarga de la API oficial de los Nobel los laureados VIVOS de ciencias y economía.
    Se renueva como mucho una vez por semana y, si falla, se usa la copia anterior."""
    if ARCHIVO_NOBEL.exists() and not forzar:
        try:
            with open(ARCHIVO_NOBEL, encoding="utf-8") as f:
                antiguo = json.load(f)
            hecho = datetime.strptime(antiguo["actualizado"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
            if datetime.now(timezone.utc) - hecho < timedelta(days=DIAS_RENOVAR_NOBEL):
                return antiguo
        except Exception:
            pass
    lista = []
    for codigo in CODIGOS_NOBEL:
        url = f"https://api.nobelprize.org/2.1/laureates?limit=1000&nobelPrizeCategory={codigo}"
        for l in json.loads(descargar(url))["laureates"]:
            if "death" in l or "orgName" in l:   # fallecidos y organizaciones fuera
                continue
            conocido = (l.get("knownName") or {}).get("en") or ""
            nombre = _sin_iniciales(conocido)
            if not nombre:
                continue
            premios = sorted(l.get("nobelPrizes", []), key=lambda p: p["awardYear"])
            categoria = premios[-1]["category"]["en"]
            ano = premios[-1]["awardYear"]
            etiqueta = f"Nobel de {CATEGORIAS_NOBEL.get(categoria, categoria)} {ano}"
            alias = {nombre}
            dado = _sin_iniciales((l.get("givenName") or {}).get("en") or "").split()
            apellido = (l.get("familyName") or {}).get("en") or ""
            if dado and apellido:
                alias.add(f"{dado[0]} {apellido}")        # 'Morten Meldal'
                alias.add(" ".join(dado) + f" {apellido}")  # 'Morten Peter Meldal'
            partes = normalizar(nombre).split()
            comun = len(partes) <= 2 and partes[0] in NOMBRES_COMUNES and partes[-1] in APELLIDOS_COMUNES
            lista.append({"nombre": nombre, "premio": etiqueta, "ambiguo": bool(comun),
                          "alias": sorted(a for a in alias if a != nombre)})
    if not lista:
        raise ValueError("la API de los Nobel no devolvió laureados")
    datos = {"actualizado": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "laureados": lista}
    with open(ARCHIVO_NOBEL, "w", encoding="utf-8") as f:
        json.dump(datos, f, ensure_ascii=False, indent=1)
    return datos


def cargar_laureados():
    """Lista combinada: Nobel desde la API oficial (si está) + Fields/Turing/Abel de laureados.json."""
    with open(ARCHIVO_LAUREADOS, encoding="utf-8") as f:
        manual = json.load(f)
    automaticos = []
    if ARCHIVO_NOBEL.exists():
        try:
            with open(ARCHIVO_NOBEL, encoding="utf-8") as f:
                automaticos = json.load(f)["laureados"]
        except Exception:
            automaticos = []
    if automaticos:
        # La API manda; lo marcado a mano como "nombre común" se respeta.
        comunes = {normalizar(d["nombre"]) for d in manual if d.get("ambiguo")}
        automaticos = [dict(d, ambiguo=d.get("ambiguo") or normalizar(d["nombre"]) in comunes)
                       for d in automaticos]
        manual = [d for d in manual if not d["premio"].startswith("Nobel")]
    return _patrones_laureados(automaticos + manual)


def _patrones_laureados(entradas):
    """Lista de (patrón, entrada) con una entrada por cada nombre o alias."""
    lista, vistos = [], set()
    for d in entradas:
        for nombre in [d["nombre"]] + list(d.get("alias", [])):
            clave = normalizar(nombre)
            if clave in vistos:
                continue
            vistos.add(clave)
            palabras = clave.split()
            if len(palabras) == 2:   # 'Morten Meldal' también vale para 'Morten Peter Meldal'
                regex = (r"(?<![a-z])" + re.escape(palabras[0]) + r"(?:\s+[a-z'.-]{1,20}){0,2}?\s+"
                         + re.escape(palabras[1]) + r"(?![a-z])")
            else:
                regex = r"(?<![a-z])" + re.escape(clave) + r"(?![a-z])"
            lista.append((re.compile(regex), d))
    return lista


# Frases que señalan QUIÉN da la charla (se comparan sin acentos y en minúsculas).
# ADELANTE: el nombre del ponente viene DESPUÉS de la frase ("impartida por X").
CUES_PONENTE_ADELANTE = re.compile(
    r"(impartid[oa]s?\s+por|a\s+cargo\s+de|ponentes?\s*:?|conferenciantes?\s*:?|invitad[oa]s?\s*:?|"
    r"ofrecid[oa]s?\s+por|presentad[oa]s?\s+por|de\s+la\s+mano\s+de|con\s+la\s+participacion\s+de|"
    r"contara\s+con|cuenta\s+con|"
    r"(?:conferencia|charla|leccion|coloquio|seminario)\s+(?:magistral\s+|inaugural\s+)?(?:de|del|por)\b|"
    r"visita\s+(?:de|del)\b|conversacion\s+con|dialogo\s+con|encuentro\s+con|"
    r"speakers?\s*:?|invited\s+speaker|talk\s+by|lecture\s+by)"
)
# ATRÁS: el nombre del ponente viene ANTES de la frase ("X ofrece una conferencia").
CUES_PONENTE_ATRAS = re.compile(
    r"(impartira|imparte|ofrecera|ofrece|pronunciara|pronuncia|dara\s+una|dara\s+la|intervienen?|"
    r"visitara|participara|protagonizara|estara\s+en|llegara\s+a|nos\s+visita|visita\s+sevilla)"
)
# Frases que dicen que la persona es el TEMA de la charla, no quien la da.
CUES_TEMA = re.compile(
    r"(concedid[oa]s?\s+a|otorgad[oa]s?\s+a|atribuid[oa]s?\s+a|"
    r"(?:sobre|acerca\s+de|en\s+torno\s+a|dedicad[oa]s?\s+a(?:l)?|centrad[oa]s?\s+en(?:\s+el)?)\s+"
    r"(?:(?:el|la|los|las|del)\s+)?(?:premio\s+)?nobel|"
    r"(?:vida\s+y\s+obra|obra|figura|legado|trabajo|descubrimientos?|contribuciones?)\s+(?:de|del)\b|"
    r"homenaje\s+a|en\s+honor\s+(?:a|de)|centenario\s+de|aniversario\s+de)"
)


def analizar_laureado(titulo, descripcion, laureados):
    """Devuelve (ponente, tema).
    ponente = laureado que parece dar la charla  -> se destaca con estrella.
    tema    = laureado del que se habla, pero la charla la da otra persona (p. ej. un
              profesor que explica el Nobel de este año)  -> solo marca suave."""
    texto = normalizar(f"{titulo} . {descripcion}")
    titulo_n = normalizar(titulo)
    contexto = bool(CONTEXTO_PREMIO.search(texto))
    v_ponente = ([(m.end(), m.end() + 120) for m in CUES_PONENTE_ADELANTE.finditer(texto)]
                 + [(max(0, m.start() - 120), m.start()) for m in CUES_PONENTE_ATRAS.finditer(texto)])
    v_tema = [(m.end(), m.end() + 80) for m in CUES_TEMA.finditer(texto)]

    def dentro(ocurrencias, ventanas):
        return any(a <= m.start() and m.end() <= b for m in ocurrencias for a, b in ventanas)

    ponente = tema = None
    for patron, d in laureados:
        if d.get("ambiguo") and not contexto:
            continue
        ocurrencias = list(patron.finditer(texto))
        if not ocurrencias:
            continue
        etiqueta = f'{d["nombre"]} ({d["premio"]})'
        if dentro(ocurrencias, v_ponente):
            ponente = ponente or etiqueta          # aparece justo donde se nombra al ponente
        elif dentro(ocurrencias, v_tema):
            tema = tema or etiqueta                # se habla de él/ella ("concedido a", "obra de"...)
        elif patron.search(titulo_n):
            ponente = ponente or etiqueta          # encabeza el título y nada indica que sea el tema
        else:
            tema = tema or etiqueta                # mencionado de pasada
    return ponente, tema


# ----------------------------------------------------------------------------
# Descarga
# ----------------------------------------------------------------------------
def descargar_bytes(url):
    peticion = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(peticion, timeout=40) as r:
        return r.read()


def descargar(url, codificacion="utf-8"):
    return descargar_bytes(url).decode(codificacion, errors="replace")


# ----------------------------------------------------------------------------
# Lectores
# ----------------------------------------------------------------------------
def leer_ics(texto):
    """Devuelve una lista de dicts con los campos de cada VEVENT."""
    texto = re.sub(r"\r?\n[ \t]", "", texto)  # une las líneas largas partidas
    eventos = []
    for bloque in re.findall(r"BEGIN:VEVENT(.*?)END:VEVENT", texto, re.S):
        campos = {}
        for linea in bloque.strip().splitlines():
            if ":" not in linea:
                continue
            clave, valor = linea.split(":", 1)
            campos[clave.split(";")[0].upper()] = valor.strip()
        eventos.append(campos)
    return eventos


def _texto_ics(valor):
    return (valor.replace("\\n", " ").replace("\\,", ",").replace("\\;", ";")
            .replace("\\\\", "\\").strip())


def _fecha_ics(valor):
    """'20261112T110000Z' -> datetime en hora de Madrid. Si es solo fecha, hora = None."""
    m = re.match(r"(\d{8})(?:T(\d{6}))?(Z?)", valor or "")
    if not m:
        return None, None
    if not m.group(2):
        return datetime.strptime(m.group(1), "%Y%m%d"), None
    dt = datetime.strptime(m.group(1) + m.group(2), "%Y%m%d%H%M%S")
    if m.group(3) == "Z":
        dt = utc_a_madrid(dt.replace(tzinfo=timezone.utc))
    return dt, True


def eventos_desde_ics(codigo, texto):
    resultado = []
    for c in leer_ics(texto):
        inicio, con_hora = _fecha_ics(c.get("DTSTART"))
        if inicio is None:
            continue
        fin, _ = _fecha_ics(c.get("DTEND"))
        uid = c.get("UID", "")
        m = re.search(r"-(\d+)@", uid)
        ident = m.group(1) if m else re.sub(r"\W+", "", uid)
        resultado.append({
            "id": f"{codigo}-{ident}",
            "titulo": html.unescape(_texto_ics(c.get("SUMMARY", ""))),
            "inicio": inicio, "fin": fin, "con_hora": bool(con_hora),
            "lugar": html.unescape(_texto_ics(c.get("LOCATION", ""))),
            "url": _texto_ics(c.get("DESCRIPTION", "")),
            "descripcion": "",
        })
    return resultado


def eventos_desde_rss(codigo, texto):
    resultado = []
    raiz = ET.fromstring(texto.encode("utf-8"))
    for item in raiz.iter("item"):
        titulo = (item.findtext("title") or "").strip()
        enlace = (item.findtext("link") or "").strip()
        fecha_txt = (item.findtext("pubDate") or "").strip()
        descripcion_html = item.findtext("description") or ""
        try:
            inicio = parsedate_to_datetime(fecha_txt).replace(tzinfo=None)  # ya viene en hora de Madrid
        except (TypeError, ValueError):
            continue
        m = re.search(r"/event_detail/(\d+)", enlace)
        ident = m.group(1) if m else re.sub(r"\W+", "", enlace)
        # El lugar es el primer párrafo de la descripción
        parrafos = re.findall(r"<p[^>]*>(.*?)</p>", descripcion_html, re.S)
        lugar = ""
        for p in parrafos:
            limpio = re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", p))).strip()
            if limpio:
                lugar = limpio
                break
        if "Sede:" in lugar:  # algunos eventos de la US empiezan con "Evento presencial... Sede: ..."
            lugar = lugar.split("Sede:", 1)[1].strip()
        texto_desc = re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", descripcion_html))).strip()
        resultado.append({
            "id": f"{codigo}-{ident}",
            "titulo": html.unescape(titulo),
            "inicio": inicio, "fin": None, "con_hora": True,
            "lugar": lugar[:120],
            "url": enlace,
            "descripcion": texto_desc,
        })
    return resultado


# ----------------------------------------------------------------------------
# Clasificación
# ----------------------------------------------------------------------------
def _excluida(titulo_norm):
    """¿El título tiene una palabra que descarta el evento (taller, curso, concierto...)?"""
    return bool(PALABRAS_EXCLUIR.search(FRASES_CURSO.sub(" ", titulo_norm)))


def clasificar(ev, laureados, hoy):
    """Devuelve (evento_final | None, motivo_descarte | None)."""
    descripcion = ev.get("descripcion") or ""
    titulo_norm = normalizar(ev["titulo"])
    lugar_norm = normalizar(ev.get("lugar") or "")

    # 1) Fecha: fuera los que ya han terminado
    ultimo_dia = (ev["fin"] or ev["inicio"]).date()
    if ultimo_dia < hoy:
        return None, "ya pasado"

    # 2) Lugar: solo Sevilla y su provincia
    if OTRAS_CIUDADES.search(lugar_norm) and "sevilla" not in lugar_norm:
        return None, "fuera de Sevilla"

    # 3) ¿Es una charla? (o la da un laureado / el título habla de un premio)
    ponente, tema = analizar_laureado(ev["titulo"], descripcion, laureados)
    menciona = bool(MENCION_PREMIO.search(normalizar(ev["titulo"] + " " + descripcion)) or ponente or tema)
    menciona_en_titulo = bool(MENCION_PREMIO.search(titulo_norm))
    excluida = _excluida(titulo_norm)
    if ev.get("es_charla") is not None:          # la web ya lo ha decidido (IBiS, Cajasol)
        es_charla = bool(ev["es_charla"])
    else:
        es_charla = bool(PALABRAS_CHARLA.search(titulo_norm)) and not excluida
        if not es_charla and ev.get("usar_descripcion") and not excluida:
            es_charla = bool(CHARLA_FUERTE.search(normalizar(descripcion[:700])))
    if not (ponente or es_charla or (menciona_en_titulo and not excluida)):
        return None, "no parece una charla"

    lugar = re.sub(r",\s*Espa[ñn]a\s*$", "", ev.get("lugar") or "").strip()
    inicio = ev["inicio"]
    final = {
        "id": ev["id"],
        "titulo": re.sub(r"\s+", " ", ev["titulo"]).strip(),
        "fecha": inicio.strftime("%Y-%m-%d"),
        "hora": inicio.strftime("%H:%M") if ev["con_hora"] else None,
        "lugar": lugar or None,
        "tipo": "charla",
        "destacado": bool(ponente),
        "laureado": ponente,
        "laureadoTema": tema,
        "mencionaNobel": menciona,
        "url": (ev.get("url") or "").replace("http://", "https://") or None,
        "fuente": ev["fuente"],
    }
    if ev["fin"] and ev["fin"].date() > inicio.date():
        final["fechaFin"] = ev["fin"].strftime("%Y-%m-%d")
    return final, None


# ----------------------------------------------------------------------------
# TORNEOS DE AJEDREZ (Delegación Sevillana + calendario FADA)
# ----------------------------------------------------------------------------
URL_FSA = "https://www.fsajedrez.com/portada.htm"
URL_FADA = "https://fadajedrez.com/wp/calendario-fada/"
NOMBRE_FSA = "Delegación Sevillana de Ajedrez"
NOMBRE_FADA = "FADA"

_MES = r"(enero|febrero|marzo|abril|mayo|junio|julio|agosto|septiembre|setiembre|octubre|noviembre|diciembre)"
MESES = {"enero": 1, "febrero": 2, "marzo": 3, "abril": 4, "mayo": 5, "junio": 6, "julio": 7,
         "agosto": 8, "septiembre": 9, "setiembre": 9, "octubre": 10, "noviembre": 11, "diciembre": 12}
RE_RANGO = re.compile(r"(\d{1,2})\s*(?:" + _MES + r")?\s*(?:-|–|al)\s*(\d{1,2})\s*" + _MES
                      + r"(?:\s*(?:de\s*)?(\d{4}))?")
RE_DIA = re.compile(r"(\d{1,2})\s*" + _MES + r"(?:\s*(?:de\s*)?(\d{4}))?")

# --- Cómo se expresa en las bases si hace falta licencia federativa -------------
# (se aplican sobre texto sin acentos y en minúsculas)
FED_EXIGE_FUERTE = [
    r"(solo|solamente|unicamente|exclusivamente)[^.]{0,40}federad",
    r"no (se )?(admit|permit|podran|pueden)\w*[^.]{0,60}no federad",
    r"(requisito|obligatori\w+|imprescindible|necesari\w+)[^.]{0,40}(estar )?federad",
    r"(deberan|tendran que|han de)\s+(estar|tener)[^.]{0,30}(federad|licencia federativa)",
    r"(estar|esten|encontrarse)\s+(en posesion de\s+)?(la\s+)?licencia federativa",
    r"licencia federativa\s+(en vigor|obligatoria)",
    r"debidamente federad",
    r"licencia(?! habilitante)[^.]{0,20}?en vigor",
]
FED_EXIGE_DEBIL = [
    r"(participantes|jugadores)\s+federad\w+\s+(que\s+)?(esten|estan|tengan|figuren|esten)",
]
FED_LIBRE = [
    r"federad\w+\s+o\s+no\b",
    r"\bno\s+federad\w+",
    r"sin\s+(estar\s+federad\w+|licencia|ficha)",
    r"aficionad\w+\s+y\s+federad\w+",
    r"federad\w+\s+y\s+aficionad\w+",
    r"licencia\s+habilitante",
    r"licencia\s+(de un dia|temporal|puntual)",
    r"abierto\s+a\s+(todos|todo|cualquier)",
]

# Palabras que no distinguen un torneo de otro al compararlos entre fuentes
PALABRAS_COMUNES = {
    "torneo", "abierto", "internacional", "ajedrez", "open", "memorial", "ciudad", "villa", "club",
    "deportivo", "rapidas", "rapida", "rapido", "sevilla", "diputacion", "provincia", "campeonato",
    "copa", "equipos", "edicion", "andaluza", "para", "entre", "sobre", "partidas",
}

MUNICIPIOS = [
    "sevilla", "alcala de guadaira", "dos hermanas", "utrera", "ecija", "moron de la frontera",
    "carmona", "mairena del aljarafe", "la rinconada", "lebrija", "coria del rio", "camas",
    "san juan de aznalfarache", "bormujos", "tomares", "los palacios y villafranca", "marchena",
    "osuna", "arahal", "cantillana", "lora del rio", "alcala del rio", "brenes", "gelves",
    "castilleja de la cuesta", "espartinas", "gines", "olivares", "sanlucar la mayor",
    "bollullos de la mitacion", "palomares del rio", "valencina de la concepcion", "salteras",
    "santiponce", "villanueva del ariscal", "la algaba", "guillena", "burguillos",
    "cazalla de la sierra", "constantina", "estepa", "la puebla de cazalla", "fuentes de andalucia",
    "paradas", "mairena del alcor", "el viso del alcor", "villaverde del rio", "la puebla del rio",
    "isla mayor", "pilas", "aznalcazar", "benacazon", "umbrete", "castilblanco de los arroyos",
    "las cabezas de san juan", "el cuervo de sevilla", "montellano", "el saucejo", "gerena",
    "aznalcollar", "tocina", "los rosales", "la campana", "lantejuela", "martin de la jara",
    "montequinto", "palmete", "el coronil", "los molares", "la luisiana", "penaflor", "badolatosa",
    "casariche", "herrera", "pedrera", "marinaleda", "gilena", "el pedroso", "alanis", "guadalcanal",
]


def plano(texto):
    """Quita acentos conservando la longitud exacta del texto (para poder recortar frases)."""
    salida = []
    for ch in texto:
        base = "".join(c for c in unicodedata.normalize("NFD", ch) if unicodedata.category(c) != "Mn")
        salida.append(base if len(base) == 1 else ch)
    return "".join(salida)


def limpiar_html(fragmento):
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", fragmento))).strip()


def limpiar_html_parrafos(fragmento):
    """Como limpiar_html, pero deja ' | ' donde acaba un párrafo, una línea o un elemento de lista."""
    f = re.sub(r"</(?:p|li|h[1-6]|div|tr|td|th)>|<br\s*/?>", " | ", fragmento, flags=re.I)
    return re.sub(r"(?:\s*\|\s*)+", " | ", limpiar_html(f)).strip(" |")


def _construir_fecha(dia, mes, anio, hoy):
    try:
        if anio:
            return date(anio, mes, dia)
        d = date(hoy.year, mes, dia)
        if d < hoy - timedelta(days=30):  # sin año: si ya pasó hace tiempo, es del año que viene
            d = date(hoy.year + 1, mes, dia)
        return d
    except ValueError:
        return None


def parsear_fechas(texto, hoy):
    """'14 Noviembre' / '11-13 diciembre' / '8-16 Enero 2027' -> (inicio, fin) o (None, None)."""
    t = plano(texto).lower()
    m = RE_RANGO.search(t)
    if m:
        d1, m1, d2, m2, anio = int(m.group(1)), m.group(2), int(m.group(3)), m.group(4), m.group(5)
        mes2 = MESES[m2]
        mes1 = MESES[m1] if m1 else mes2
        anio = int(anio) if anio else None
        fin = _construir_fecha(d2, mes2, anio, hoy)
        if fin is None:
            return None, None
        anio_ini = fin.year - 1 if mes1 > mes2 else fin.year
        ini = _construir_fecha(d1, mes1, anio_ini, hoy)
        return ini, fin
    m = RE_DIA.search(t)
    if m:
        ini = _construir_fecha(int(m.group(1)), MESES[m.group(2)], int(m.group(3)) if m.group(3) else None, hoy)
        return ini, None
    return None, None


def detectar_federacion(texto):
    """Devuelve (estado, frase): estado = 'exige' | 'libre' | 'sin_confirmar'."""
    orig = re.sub(r"\s+", " ", texto)
    t = plano(orig).lower()

    def buscar(patrones):
        for p in patrones:
            m = re.search(p, t)
            if m:
                a, b = max(0, m.start() - 70), min(len(orig), m.end() + 90)
                return ("..." + orig[a:b].strip() + "...")[:220]
        return None

    fuerte, debil, libre = buscar(FED_EXIGE_FUERTE), buscar(FED_EXIGE_DEBIL), buscar(FED_LIBRE)
    if fuerte:
        return "exige", fuerte
    if libre and debil:
        return "sin_confirmar", "Las bases son ambiguas: " + libre
    if libre:
        return "libre", libre
    if debil:
        return "exige", debil
    return "sin_confirmar", "Las bases no mencionan la licencia federativa"


def leer_pdf(url):
    if PdfReader is None:
        raise RuntimeError("falta instalar pypdf (pip install pypdf)")
    datos = descargar_bytes(url)
    if not datos.startswith(b"%PDF"):
        raise ValueError("no es un PDF")
    lector = PdfReader(io.BytesIO(datos))
    return " ".join((p.extract_text() or "") for p in lector.pages[:8])


def buscar_pdf_bases(url, nivel=0):
    """Busca en una página web el PDF de las bases (también siguiendo un enlace 'Bases')."""
    pagina = descargar(url)
    enlaces = [(urljoin(url, html.unescape(h)), limpiar_html(t))
               for h, t in re.findall(r'<a\s[^>]*href="([^"]+)"[^>]*>(.*?)</a>', pagina, re.S | re.I)]
    pdfs = []
    for h in [u for u, _ in enlaces] + [urljoin(url, html.unescape(u))
                                          for u in re.findall(r'href="([^"]+\.pdf)"', pagina, re.I)]:
        if h.lower().split("?")[0].endswith(".pdf") and h not in pdfs:
            pdfs.append(h)
    if pdfs:
        return next((h for h in pdfs if "base" in h.lower()), pdfs[0])
    if nivel == 0:
        for h, t in enlaces:
            if re.match(r"bases?\b", plano(t).lower()) and h.split("#")[0] != url:
                encontrado = buscar_pdf_bases(h, 1)
                if encontrado:
                    return encontrado
    return None


def leer_bases(url):
    """Devuelve el texto de las bases, sea un PDF, una página que enlaza un PDF o un Google Doc."""
    m = re.match(r"https://docs\.google\.com/document/d/([\w-]+)", url)
    if m:
        texto = descargar(f"https://docs.google.com/document/d/{m.group(1)}/export?format=txt")
        if texto.lstrip().lower().startswith(("<!doctype", "<html")):
            raise ValueError("el documento de Google no es público")
        return texto
    if url.lower().split("?")[0].endswith(".pdf"):
        return leer_pdf(url)
    pdf = buscar_pdf_bases(url)
    if not pdf:
        raise ValueError("la página no enlaza ningún PDF de bases")
    return leer_pdf(pdf)


def claves_titulo(titulo, comunes=PALABRAS_COMUNES):
    palabras = re.findall(r"[a-z0-9]+", normalizar(titulo))
    return {p for p in palabras if len(p) >= 4 and p not in comunes
            and not re.fullmatch(r"[ivxlc]+", p) and not p.isdigit()}


def municipio_en(texto):
    t = " " + re.sub(r"[^a-z0-9]+", " ", normalizar(texto)) + " "
    for m in sorted(MUNICIPIOS, key=len, reverse=True):  # primero los nombres largos
        if f" {m} " in t:
            return m.title().replace(" De ", " de ").replace(" Del ", " del ").replace(" La ", " la ") \
                .replace(" Y ", " y ").replace(" Los ", " los ")
    return None


def torneos_desde_fsa(hoy):
    """Bloque 'PRÓXIMOS TORNEOS' de la portada de la Delegación Sevillana."""
    pagina = descargar(URL_FSA, "cp1252")
    i = pagina.upper().find("PRÓXIMOS TORNEOS")
    if i < 0:
        i = plano(pagina).upper().find("PROXIMOS TORNEOS")
    if i < 0:
        raise ValueError("no encuentro el bloque 'Próximos torneos' (¿han cambiado la web?)")
    resto = pagina[i + 15:]
    fin = resto.find('bgcolor="#00FFFF"')
    bloque = resto[:fin] if fin > 0 else resto[:20000]
    ignorar = {"cartel", "chess-results", "chess results", "info64", "resultados"}
    resultado = []
    for fila in re.findall(r"<tr[^>]*>(.*?)</tr>", bloque, re.S | re.I):
        enlaces = [(html.unescape(h).strip(), limpiar_html(t))
                   for h, t in re.findall(r'<a\s[^>]*href="([^"]*)"[^>]*>(.*?)</a>', fila, re.S | re.I)]
        titulo = next(((h, t) for h, t in enlaces if t and normalizar(t) not in ignorar), None)
        if not titulo:
            continue
        sin_enlaces = re.sub(r"<a\s.*?</a>", " ", fila, flags=re.S | re.I)
        ini, fin_f = parsear_fechas(limpiar_html(sin_enlaces), hoy)
        if not ini:
            continue
        url_t = urljoin(URL_FSA, titulo[0])
        info = next((urljoin(URL_FSA, h) for h, t in enlaces
                     if "chess-results" in h.lower() or "info64" in h.lower()), None)
        nombre_pdf = url_t.rsplit("/", 1)[-1].rsplit(".", 1)[0] if url_t.lower().endswith(".pdf") else None
        resultado.append({
            "origen": "fsa", "titulo": titulo[1], "ini": ini, "fin": fin_f,
            "bases": url_t if url_t.lower().endswith(".pdf") else None,
            "web": None if url_t.lower().endswith(".pdf") else url_t,
            "info": info, "lugar": None, "formato": None,
            "id": "fsa-" + (nombre_pdf or re.sub(r"\W+", "", normalizar(titulo[1]))[:30]),
        })
    return resultado


def torneos_desde_fada(hoy):
    """Tarjetas del calendario FADA, solo las de la provincia de Sevilla."""
    pagina = descargar(URL_FADA)
    inicios = [m.start() for m in re.finditer(r'class="fada-card"', pagina)]
    if not inicios:
        raise ValueError("no encuentro tarjetas de torneos (¿han cambiado la web?)")
    trozos = [pagina[a:b] for a, b in zip(inicios, inicios[1:] + [inicios[-1] + 8000])]
    resultado = []
    for c in trozos:
        prov = re.search(r'fada-prov">(.*?)</div>', c, re.S)
        if not prov or "sevilla" not in plano(limpiar_html(prov.group(1))).lower():
            continue
        ident = re.search(r'id="fada-card-(\d+)"', c)
        ini = re.search(r'data-ini="(\d{4}-\d{2}-\d{2})"', c)
        fin = re.search(r'data-fin="(\d{4}-\d{2}-\d{2})"', c)
        titulo = re.search(r'fada-titulo">(.*?)</div>', c, re.S)
        if not (ident and ini and titulo):
            continue
        datos = {limpiar_html(k): limpiar_html(v)
                 for k, v in re.findall(r'fada-lbl">(.*?)</div>\s*<div class="fada-val">(.*?)</div>', c, re.S)}
        bases = info = web = None
        for h, t in re.findall(r'<a href="([^"]*)"[^>]*class="fada-link">(.*?)</a>', c, re.S):
            h, t = html.unescape(h), plano(limpiar_html(t)).lower()
            if "bases" in t:
                bases = h
            elif "chess" in t:
                info = info or h
            elif "web" in t:
                web = h
        ini_d = datetime.strptime(ini.group(1), "%Y-%m-%d").date()
        fin_d = datetime.strptime(fin.group(1), "%Y-%m-%d").date() if fin else None
        resultado.append({
            "origen": "fada", "titulo": limpiar_html(titulo.group(1)), "ini": ini_d,
            "fin": fin_d if fin_d and fin_d != ini_d else None,
            "bases": bases, "web": web, "info": info,
            "lugar": datos.get("Lugar"), "formato": datos.get("Formato"),
            "id": "fada-" + ident.group(1),
        })
    return resultado


def _son_el_mismo(a, b):
    if abs((a["ini"] - b["ini"]).days) > 1:
        return False
    return bool(claves_titulo(a["titulo"]) & claves_titulo(b["titulo"]))


def fusionar_torneos(fada, fsa):
    """FADA manda (fechas y lugar exactos); la Delegación aporta los que FADA no lista."""
    salida = []
    for f in fada:
        f = dict(f, fuentes=[NOMBRE_FADA], otros_ids=[], bases_alt=None)
        for s in fsa:
            if s.get("usado") or not _son_el_mismo(f, s):
                continue
            s["usado"] = True
            f["fuentes"].append(NOMBRE_FSA)
            f["otros_ids"].append(s["id"])
            f["bases_alt"] = s["bases"]
            f["info"] = f["info"] or s["info"]
            f["web"] = f["web"] or s["web"]
            if f["titulo"].isupper():  # los títulos de FADA vienen en MAYÚSCULAS
                f["titulo"] = s["titulo"]
        salida.append(f)
    for s in fsa:
        if not s.get("usado"):
            salida.append(dict(s, fuentes=[NOMBRE_FSA], otros_ids=[], bases_alt=None))
    return salida


def torneo_a_evento(t, hoy, cache_pdf):
    ultimo = t["fin"] or t["ini"]
    if ultimo < hoy:
        return None
    # Federación: se leen las bases en PDF (primero la de la Delegación, luego la de FADA)
    estado, nota = "sin_confirmar", "No hay bases publicadas que se puedan leer"
    texto_bases, errores = "", []
    for url in dict.fromkeys(u for u in (t["bases"], t["bases_alt"], t["web"]) if u):
        if url not in cache_pdf:
            try:
                cache_pdf[url] = leer_bases(url)
            except Exception as e:
                cache_pdf[url] = None
                errores.append(str(e)[:80])
        if cache_pdf[url]:
            texto_bases = cache_pdf[url]
            break
    if texto_bases.strip():
        estado, nota = detectar_federacion(texto_bases)
    elif errores:
        nota = "No se pudieron leer las bases (" + errores[0] + ")"
    lugar = t["lugar"]
    if not lugar:
        base = ""
        n_ = plano(texto_bases).lower()
        for palabra in ("local de juego", "lugar", "sede"):
            k = n_.find(palabra)
            if k >= 0:
                base = texto_bases[k:k + 300]
                break
        lugar = municipio_en(t["titulo"]) or municipio_en(base) or "Provincia de Sevilla"
    ev = {
        "id": t["id"],
        "titulo": re.sub(r"\s+", " ", t["titulo"]).strip(),
        "fecha": t["ini"].strftime("%Y-%m-%d"),
        "hora": None,
        "lugar": lugar,
        "tipo": "torneo",
        "destacado": False,
        "federacion": estado,
        "federacionNota": nota,
        "formato": t["formato"],
        "url": t["bases"] or t["bases_alt"] or t["web"],
        "urlInfo": t["info"],
        "fuente": " + ".join(t["fuentes"]),
    }
    if t["fin"] and t["fin"] > t["ini"]:
        ev["fechaFin"] = t["fin"].strftime("%Y-%m-%d")
    if t["otros_ids"]:
        ev["otrosIds"] = t["otros_ids"]
    return ev


def recolectar_torneos(hoy):
    """Devuelve (lista_de_eventos, fuentes_leidas_ok, nombres_de_fuentes_que_fallaron)."""
    fada, fsa, ok, fallidas = [], [], 0, []
    for nombre, funcion, destino in ((NOMBRE_FADA, torneos_desde_fada, fada),
                                      (NOMBRE_FSA, torneos_desde_fsa, fsa)):
        try:
            destino.extend(funcion(hoy))
            ok += 1
            print(f"[OK] {nombre}: {len(destino)} torneos leídos")
        except Exception as e:
            print(f"[FALLO] {nombre}: {e}")
            fallidas.append(nombre)
            if "CERTIFICATE_VERIFY_FAILED" in str(e):
                print("        -> Problema de certificados de tu PC. Ejecuta:  pip install truststore")
    if PdfReader is None:
        print("[AVISO] Falta 'pypdf': no se leerán las bases. Ejecuta:  pip install pypdf")
    cache_pdf, eventos = {}, []
    for t in fusionar_torneos(fada, fsa):
        ev = torneo_a_evento(t, hoy, cache_pdf)
        if ev:
            eventos.append(ev)
    return eventos, ok, fallidas


# ----------------------------------------------------------------------------
# CHARLAS DE LAS WEBS: DivulgaUS, IBiS, Facultad de Física y Fundación Cajasol
# (cada lector tiene una parte que SOLO interpreta el HTML y otra que descarga)
# ----------------------------------------------------------------------------
PAUSA = 0.2          # segundos de espera entre peticiones a una misma web (por educación)
MAX_FICHAS = 45      # máximo de fichas de detalle que se abren por web en cada ejecución
SEMANAS_DIVULGAUS = 10

URL_DIVULGAUS = "https://www.investigacion.us.es"
URL_IBIS = "https://www.ibis-sevilla.es"
URL_FISICA = "https://fisica.us.es"
URL_CAJASOL = "https://fundacioncajasol.com"
NOMBRE_DIVULGAUS = "DivulgaUS (Universidad de Sevilla)"
NOMBRE_IBIS = "IBiS (Instituto de Biomedicina de Sevilla)"
NOMBRE_FISICA = "Facultad de Física (US)"
NOMBRE_CAJASOL = "Fundación Cajasol"

MESES_ABREVIADOS = {"ene": 1, "jan": 1, "feb": 2, "mar": 3, "abr": 4, "apr": 4, "may": 5, "jun": 6,
                    "jul": 7, "ago": 8, "aug": 8, "sep": 9, "set": 9, "oct": 10, "nov": 11,
                    "dic": 12, "dec": 12}


def _pausa():
    time.sleep(PAUSA)


def _slug(url):
    """Último trozo de la dirección, usable como identificador (si es muy largo se acorta con un código)."""
    partes = [p for p in url.split("?")[0].split("/") if p]
    slug = partes[-1] if partes else re.sub(r"\W+", "", url)
    if len(slug) > 100:
        slug = slug[:90] + "-" + hashlib.md5(slug.encode("utf-8")).hexdigest()[:6]
    return slug


# --- Fecha, hora y lugar dentro de un texto libre ---------------------------------
_ETIQUETAS = (r"(?:cuando|fecha|dia|hora|horario|ponentes?|entrada|entradas|inscripcion|inscripciones|"
              r"organiza|organizan|precio|duracion|cargo|aforo|mas informacion|acceso|contacto|idioma|"
              r"modalidad|titulo|resumen)\s*:")
RE_HORAS = [
    re.compile(r"\b(?:hora|horario)\s*:?\s*(?:de\s+)?(\d{1,2})\s*[:.h]\s*(\d{2})\b"),
    re.compile(r"\ba\s+las?\s+(\d{1,2})\s*[:.h]\s*(\d{2})\b"),
    re.compile(r"\b(\d{1,2})\s*[:.]\s*(\d{2})\s*(?:h\b|hs\b|hrs?\b|horas\b)"),
    re.compile(r"\ba\s+las?\s+(\d{1,2})\s*(?:h\b|hs\b|hrs?\b|horas?\b)()"),
    re.compile(r"\b(?:hora|horario)\s*:?\s*(\d{1,2})\s*(?:h\b|hs\b|hrs?\b|horas?\b)()"),
]
_CORTE_FRASE = re.compile(r"(?<!Avda)(?<!Av)(?<!C)(?<!Pl)(?<!Dr)(?<!Dra)(?<!Prof)(?<!Sr)(?<!Sra)"
                          r"\.\s+(?=[A-ZÁÉÍÓÚÑ¿¡])")


def buscar_hora(t):
    """t = texto sin acentos y en minúsculas. Devuelve 'HH:MM' o None."""
    for patron in RE_HORAS:
        m = patron.search(t)
        if m:
            h, mi = int(m.group(1)), int(m.group(2) or 0)
            if 0 <= h <= 23 and 0 <= mi <= 59:
                return f"{h:02d}:{mi:02d}"
    return None


def _limpiar_lugar(candidato):
    candidato = candidato.split(" | ")[0]
    candidato = _CORTE_FRASE.split(candidato.strip(), 1)[0]
    candidato = re.sub(r"\s+", " ", candidato).strip(" .;,:-–")
    candidato = re.sub(r"\s*\($", "", candidato)
    return candidato[:110].rstrip(" ,;:") or None


def extraer_fecha_hora_lugar(texto, hoy):
    """Busca en el texto de una ficha 'Cuándo/Fecha/Día', 'Hora' y 'Lugar/Sede'.
    Devuelve (fecha|None, 'HH:MM'|None, lugar|None)."""
    orig = re.sub(r"\s+", " ", texto)
    t = plano(orig).lower()
    if len(t) != len(orig):          # por si algún carácter raro cambia la longitud
        t = orig.lower()
    fecha = None
    m = re.search(r"\b(?:cuando|fecha|dia|fecha y hora)\s*:\s*(?:[a-z]+,?\s+)?(\d{1,2})\s+(?:de\s+)?" + _MES
                  + r"(?:\s+(?:de\s+|del\s+)?(\d{4}))?", t)
    if m:
        fecha = _construir_fecha(int(m.group(1)), MESES[m.group(2)], int(m.group(3)) if m.group(3) else None, hoy)
    hora = buscar_hora(t)
    lugar = None
    m = re.search(r"\b(?:lugar|sede|donde|ubicacion|localizacion)(?:\s+de\s+\w+)?\s*:\s*", t)
    if m:
        resto = t[m.end():]
        corte = re.search(_ETIQUETAS, resto)
        fin = corte.start() if corte else len(resto)
        lugar = _limpiar_lugar(orig[m.end(): m.end() + min(fin, 200)])
    else:
        m = re.search(r"(?:\ba\s+las?\s+\d{1,2}(?:\s*[:.h]\s*\d{2})?\s*(?:h\b|hs\b|horas?\b)?|\bhoras?)\s*,?\s+"
                      r"en\s+(?:el|la|las|los)?\s*", t)
        if m:
            lugar = _limpiar_lugar(orig[m.end(): m.end() + 160])
    if lugar:
        lugar = lugar[0].upper() + lugar[1:]
    return fecha, hora, lugar


def _inicio_etiqueta(pagina, marca, desde=0):
    """Posición del '<' de la etiqueta que contiene 'marca' (o -1 si no está)."""
    i = pagina.find(marca, desde)
    return pagina.rfind("<", 0, i) if i >= 0 else -1


def _con_hora(dt, hora):
    """Devuelve dt con la hora 'HH:MM' puesta."""
    return dt.replace(hour=int(hora[:2]), minute=int(hora[3:5]), second=0, microsecond=0)


# --- DivulgaUS (Vicerrectorado de Investigación de la US) -------------------------
DUROS_DIVULGAUS = re.compile(r"\b(taller|escape|exposicion|teatro|concierto|visita|musical|espectaculo|cine|"
                             r"proyeccion|olimpiada|yincana|gymkana|torneo|feria|monologo)")


def parsear_semana_divulgaus(pagina):
    """Vista semanal del calendario -> lista de (href, titulo, inicio_en_hora_de_Madrid, tiene_hora)."""
    salida = []
    for href, titulo, iso in re.findall(r'<a href="(/eventos/[^"]+)"[^>]*>(.*?)</a>\s*<time datetime="([^"]+)"',
                                         pagina, re.S):
        try:
            dt = datetime.strptime(iso[:19], "%Y-%m-%dT%H:%M:%S")
        except ValueError:
            continue
        # Si los segundos no son 0, no es una hora real (es la hora a la que se creó la ficha)
        salida.append((href, limpiar_html(titulo), utc_a_madrid(dt.replace(tzinfo=timezone.utc)), dt.second == 0))
    return salida


def parsear_ficha_divulgaus(pagina):
    """Ficha de un evento -> texto (entradilla + cuerpo)."""
    i = _inicio_etiqueta(pagina, 'class="node__content"')
    j = pagina.find("</article>", i)
    bloque = pagina[i:j] if i >= 0 and j > i else pagina
    bloque = re.sub(r'<h3 class="field__label">.*?</h3>', " ", bloque, flags=re.S)
    texto = limpiar_html_parrafos(bloque)
    return re.sub(r"^\w{3}, \d\d/\d\d/\d{4} - \d\d:\d\d\s*\|?\s*", "", texto)


def eventos_divulgaus(hoy):
    inicio_semana = hoy - timedelta(days=hoy.weekday())
    candidatos, fallos = {}, 0
    for i in range(SEMANAS_DIVULGAUS):
        anio, semana, _ = (inicio_semana + timedelta(weeks=i)).isocalendar()
        try:
            pagina = descargar(f"{URL_DIVULGAUS}/calendar-field_fecha_evento/week/{anio}{semana:02d}")
            if "calendar-calendar" not in pagina:
                raise ValueError("el calendario no tiene el formato de siempre (¿han cambiado la web?)")
        except urllib.error.HTTPError as e:
            if e.code == 404:        # la web no tiene página para algunas semanas (p. ej. la 53): vacía
                continue
            if i == 0:
                raise
            fallos += 1
            continue
        except Exception:
            if i == 0:
                raise
            fallos += 1
            continue
        for href, titulo, inicio, con_hora in parsear_semana_divulgaus(pagina):
            if inicio.date() >= hoy:
                candidatos.setdefault(href, (titulo, inicio, con_hora))
        _pausa()
    if fallos:
        print(f"[AVISO] DivulgaUS: {fallos} semanas no se pudieron leer")
    resultado, abiertas = [], 0
    for href, (titulo, inicio, con_hora) in sorted(candidatos.items(), key=lambda kv: kv[1][1]):
        t_norm = normalizar(titulo)
        texto = ""
        if abiertas < MAX_FICHAS and not (DUROS_DIVULGAUS.search(t_norm) and not MENCION_PREMIO.search(t_norm)):
            try:
                texto = parsear_ficha_divulgaus(descargar(URL_DIVULGAUS + href))
            except Exception:
                texto = ""
            abiertas += 1
            _pausa()
        _, hora, lugar = extraer_fecha_hora_lugar(texto, hoy) if texto else (None, None, None)
        if not con_hora and hora:
            inicio, con_hora = _con_hora(inicio, hora), True
        resultado.append({
            "id": "divulgaus-" + _slug(href), "titulo": titulo, "inicio": inicio, "fin": None,
            "con_hora": con_hora, "lugar": lugar or "", "url": URL_DIVULGAUS + href,
            "descripcion": texto, "fuente": NOMBRE_DIVULGAUS, "usar_descripcion": True,
        })
    return resultado


# --- IBiS (Instituto de Biomedicina de Sevilla) ------------------------------------
IBIS_NO_CHARLA = re.compile(r"consortium|meeting|jornada|curso|workshop|congreso|formativ|escuela|reunion|"
                            r"asamblea|simposio|symposium|master|doctorado")
IBIS_SI_CHARLA = re.compile(r"seminar|forum|foro|sesion|charla|conferencia|lecture|coloquio")


def parsear_listado_ibis(pagina):
    """Listado de eventos -> lista de (href, titulo)."""
    salida = []
    for art in re.findall(r'<article class="event-itemlist">(.*?)</article>', pagina, re.S):
        m = re.search(r'event-itemlist--title"><a href="([^"]+)">(.*?)</a>', art, re.S)
        if m:
            salida.append((html.unescape(m.group(1)), limpiar_html(m.group(2))))
    return salida


def parsear_ficha_ibis(pagina):
    """Ficha de un evento -> dict con inicio, fin, lugar, organizador, ponentes y categoría."""
    filas = {}
    for k, v in re.findall(r"<tr>\s*<th[^>]*>(.*?)</th>\s*<td[^>]*>(.*?)</td>\s*</tr>", pagina, re.S):
        filas[plano(limpiar_html(k)).lower()] = limpiar_html(v)
    fecha_txt = next((v for k, v in filas.items() if k.startswith("fecha")), "")
    momentos = []
    for d, mes, a, h, mi in re.findall(r"(\d{1,2})/(\d{1,2})/(\d{4})\s+(\d{1,2}):(\d{2})", fecha_txt):
        try:
            momentos.append(datetime(int(a), int(mes), int(d), int(h), int(mi)))
        except ValueError:
            pass
    categorias = re.findall(r'<li class="breadcrumb-item"><a href="[^"]+">(.*?)</a></li>', pagina, re.S)
    return {
        "inicio": momentos[0] if momentos else None,
        "fin": momentos[1] if len(momentos) > 1 else None,
        "lugar": filas.get("lugar", ""),
        "organizador": filas.get("organizador", ""),
        "ponentes": filas.get("ponentes", ""),
        "categoria": limpiar_html(categorias[-1]) if categorias else "",
    }


def es_charla_ibis(titulo, ficha):
    tit = plano(titulo).lower()
    cat = plano(ficha["categoria"]).lower()
    if IBIS_NO_CHARLA.search(tit + " " + cat):
        return False
    if IBIS_SI_CHARLA.search(tit + " " + cat):
        return True
    return bool(ficha["ponentes"])


def eventos_ibis(hoy):
    pagina = descargar(URL_IBIS + "/es/eventos/")
    resultado = []
    for href, titulo in parsear_listado_ibis(pagina)[:MAX_FICHAS]:
        url = urljoin(URL_IBIS, href)
        try:
            ficha = parsear_ficha_ibis(descargar(url))
        except Exception:
            continue
        _pausa()
        if not ficha["inicio"]:
            continue
        fin = ficha["fin"]
        if fin and (fin.date() - ficha["inicio"].date()).days > 3:
            continue            # varios días seguidos: congreso o curso, no una charla
        descripcion = " ".join(x for x in (
            ficha["organizador"] and "Organiza: " + ficha["organizador"],
            ficha["ponentes"] and "Ponentes: " + ficha["ponentes"],
            ficha["categoria"]) if x)
        resultado.append({
            "id": "ibis-" + _slug(url), "titulo": titulo, "inicio": ficha["inicio"], "fin": fin,
            "con_hora": True, "lugar": ficha["lugar"], "url": url, "descripcion": descripcion,
            "fuente": NOMBRE_IBIS, "es_charla": es_charla_ibis(titulo, ficha),
        })
    return resultado


# --- Facultad de Física (US) ---------------------------------------------------------
def parsear_listado_fisica(pagina):
    """Listado de noticias -> lista de (fecha_de_la_noticia, href, titulo)."""
    salida = []
    for iso, href, titulo in re.findall(
            r'<time datetime="([^"]+)"[^>]*>[^<]*</time>\s*</div>\s*'
            r'<h4 class="noticias__texto-titulo"><a href="([^"]+)"[^>]*>(.*?)</a>', pagina, re.S):
        try:
            fecha = datetime.strptime(iso[:10], "%Y-%m-%d").date()
        except ValueError:
            continue
        salida.append((fecha, html.unescape(href), limpiar_html(titulo)))
    return salida


def parsear_ficha_fisica(pagina):
    """Ficha de una noticia -> texto del cuerpo."""
    i = _inicio_etiqueta(pagina, "field--name-body")
    j = pagina.find("</article>", i)
    if i < 0:
        return ""
    return limpiar_html_parrafos(pagina[i:j if j > i else i + 8000])


def eventos_fisica(hoy):
    pagina = descargar(URL_FISICA + "/noticias")
    if "noticias__texto-titulo" not in pagina:
        raise ValueError("no encuentro las noticias (¿han cambiado la web?)")
    resultado = []
    for fecha_lista, href, titulo in parsear_listado_fisica(pagina)[:MAX_FICHAS]:
        url = urljoin(URL_FISICA, href)
        try:
            texto = parsear_ficha_fisica(descargar(url))
        except Exception:
            continue
        _pausa()
        # Las noticias suelen ser de hace meses: el año que falta se decide con la fecha del listado
        fecha_txt, hora, lugar = extraer_fecha_hora_lugar(texto, fecha_lista)
        fecha = fecha_txt if fecha_txt and abs((fecha_txt - fecha_lista).days) <= 90 else fecha_lista
        inicio = datetime(fecha.year, fecha.month, fecha.day, 0, 0)
        if hora:
            inicio = _con_hora(inicio, hora)
        resultado.append({
            "id": "fisica-" + _slug(url), "titulo": titulo, "inicio": inicio, "fin": None,
            "con_hora": bool(hora), "lugar": lugar or "Facultad de Física, Universidad de Sevilla",
            "url": url, "descripcion": texto, "fuente": NOMBRE_FISICA, "usar_descripcion": True,
        })
    return resultado


# --- Fundación Cajasol (solo Sevilla; solo lo que parece charla de ciencia) ------------
CAJASOL_TIPOS = re.compile(r"charla|conferencia|conversacion|encuentro|coloquio|mesa redonda|jornada|debate|"
                           r"leccion|ponencia|presentacion|evento literario|foro|nobel|cienc|cientific|"
                           r"investigador|catedratic")
CAJASOL_CIENCIA = re.compile(r"\b(ciencias?|cientific[oa]s?|investigador[a-z]*|catedratic[oa]s?|universidad|"
                             r"nobel|astrofisic[oa]|fisic[oa]s?|quimic[oa]s?|biolog[oa]s?|matematic[oa]s?|"
                             r"neurocienc[a-z]*|ingenier[oa]s?|medicina|genetic[oa]|divulgad[a-z]*)\b")


def _bonito(titulo):
    """'ANCLAJE: ADICCIÓN Y JUVENTUD' -> 'Anclaje: Adicción y Juventud' (solo si viene todo en mayúsculas)."""
    if not titulo.isupper():
        return titulo
    chicas = {"y", "de", "del", "la", "el", "los", "las", "en", "a", "o", "un", "una", "por", "con", "al", "e"}
    def capitalizar(p):
        for k, ch in enumerate(p):
            if ch.isalpha():
                return p[:k] + ch.upper() + p[k + 1:]
        return p

    palabras = titulo.lower().split(" ")
    return " ".join(p if (i > 0 and p in chicas) else capitalizar(p) for i, p in enumerate(palabras))


def _fecha_futura(dia, mes, hoy):
    """Fecha sin año de un listado de próximos eventos: si ya pasó, es del año que viene."""
    try:
        d = date(hoy.year, mes, dia)
    except ValueError:
        return None
    return d if d >= hoy - timedelta(days=1) else date(hoy.year + 1, mes, dia)


def parsear_listado_cajasol(pagina, hoy):
    """Listado de eventos -> lista de dicts (sin repetidos; el listado trae cada tarjeta dos veces)."""
    salida, vistos = [], set()
    for href, bloque in re.findall(r'<a href="([^"]+)" class="event-item">(.*?)</a>', pagina, re.S):
        m = re.search(r'<span class="date h3"><span class="text-light">(\d{1,2})\s+([A-ZÑ]{3})</span>(.*?)</span>',
                      bloque, re.S)
        ciudad = re.search(r'class="place[^"]*">(.*?)</span>', bloque, re.S)
        if not m or not ciudad or plano(limpiar_html(ciudad.group(1))).lower() != "sevilla":
            continue
        dia, mes = int(m.group(1)), MESES_ABREVIADOS.get(plano(m.group(2)).lower())
        if not mes:
            continue
        resto = limpiar_html(m.group(3))
        hora = fin = None
        mh = re.fullmatch(r"(\d{1,2}):(\d{2})", resto)
        mf = re.fullmatch(r"(\d{1,2})\s+([A-ZÑ]{3})", resto)
        if mh:
            hora = f"{int(mh.group(1)):02d}:{mh.group(2)}"
            ini = _fecha_futura(dia, mes, hoy)
        elif mf and MESES_ABREVIADOS.get(plano(mf.group(2)).lower()):
            mes_fin = MESES_ABREVIADOS[plano(mf.group(2)).lower()]
            fin = _fecha_futura(int(mf.group(1)), mes_fin, hoy)
            try:
                ini = date(fin.year if mes <= mes_fin else fin.year - 1, mes, dia)
            except (ValueError, AttributeError):
                ini = None
        else:
            ini = _fecha_futura(dia, mes, hoy)
        if not ini:
            continue
        clave = (href, ini)
        if clave in vistos:
            continue
        vistos.add(clave)
        campo = lambda c: (lambda x: limpiar_html(x.group(1)) if x else "")(
            re.search(r'class="' + c + r'">(.*?)</span>', bloque, re.S))
        salida.append({"href": href, "tipo": campo("subtitle h6"), "titulo": campo("title h3"),
                       "subtitulo": campo("title h4"), "ini": ini, "fin": fin, "hora": hora})
    return salida


def parsear_ficha_cajasol(pagina):
    """Ficha de un evento -> texto de la descripción."""
    i = _inicio_etiqueta(pagina, 'class="text-holder"', max(0, pagina.find('class="content-holder"')))
    j = pagina.find("</section>", i)
    return limpiar_html_parrafos(pagina[i:j]) if i >= 0 and j > i else ""


def eventos_cajasol(hoy):
    pagina = descargar(URL_CAJASOL + "/eventos/")
    if 'class="event-item"' not in pagina:
        raise ValueError("no encuentro los eventos (¿han cambiado la web?)")
    resultado, abiertas = [], 0
    for c in parsear_listado_cajasol(pagina, hoy):
        todo = plano(f"{c['tipo']} {c['titulo']} {c['subtitulo']}").lower()
        if not CAJASOL_TIPOS.search(todo) or abiertas >= MAX_FICHAS:
            continue
        try:
            texto = parsear_ficha_cajasol(descargar(c["href"]))
        except Exception:
            continue
        abiertas += 1
        _pausa()
        _, hora, lugar = extraer_fecha_hora_lugar(texto, hoy)
        hora = c["hora"] or hora
        inicio = datetime(c["ini"].year, c["ini"].month, c["ini"].day, 0, 0)
        if hora:
            inicio = _con_hora(inicio, hora)
        titulo = " — ".join(_bonito(x) for x in (c["titulo"], c["subtitulo"]) if x)
        # Cajasol es una fundación cultural: solo cuentan las charlas con aire científico
        es_ciencia = bool(CAJASOL_CIENCIA.search(normalizar(titulo + " " + texto)))
        fin = datetime(c["fin"].year, c["fin"].month, c["fin"].day) if c["fin"] else None
        resultado.append({
            "id": f"cajasol-{_slug(c['href'])}-{c['ini'].strftime('%Y%m%d')}",
            "titulo": titulo, "inicio": inicio, "fin": fin, "con_hora": bool(hora),
            "lugar": lugar or "Fundación Cajasol, Sevilla", "url": c["href"], "descripcion": texto,
            "fuente": NOMBRE_CAJASOL, "es_charla": es_ciencia,
        })
    return resultado


# ----------------------------------------------------------------------------
# PRENSA: pistas de visitas de laureados (Google Noticias)
# ----------------------------------------------------------------------------
PRENSA_CONSULTAS = [
    "nobel Sevilla when:45d",
    '"premio nobel" "Universidad de Sevilla" when:60d',
    '"premio nobel" "Pablo de Olavide" when:60d',
    '"medalla Fields" OR "premio Turing" OR "premio Abel" Sevilla when:90d',
    "nobel conferencia Sevilla universidad when:45d",
]
PRENSA_DIAS = 45
PRENSA_MAXIMO = 12
PRENSA_RUIDO = re.compile(r"nobel de (?:la )?paz|premios? nobel de literatura|nobel de literatura")
PRENSA_PREMIO = re.compile(r"\b(nobel|medalla fields|premio turing|premio abel)\b")
PRENSA_ACCION = re.compile(r"\b(conferencia|charla|visita|visitara|visitan|recibe|recibira|ofrece|ofrecera|"
                           r"imparte|impartira|pronunciara|llega|llegara|estara|honoris|investid[oa]|leccion|"
                           r"coloquio|encuentro|clase magistral|distincion|acoge|acogera|inaugura|inaugurara|"
                           r"participa|participara|conversacion|dialogo|ponencia|ciclo)\b")
PRENSA_LOCAL = re.compile(r"\b(sevilla|sevillan[oa]s?|hispalense|us|upo|olavide|andalucia|andaluz[a-z]*|"
                          r"cajasol|dos hermanas|alcala de guadaira|maestranza|cartuja|ciccartuja|cabd|ibis|ibvf|"
                          r"csic)\b")


def pistas_desde_rss(texto, hoy, laureados):
    """Noticias de Google Noticias (RSS) que parecen hablar de un laureado en Sevilla."""
    raiz = ET.fromstring(texto.encode("utf-8"))
    pistas = []
    for item in raiz.iter("item"):
        titulo = html.unescape((item.findtext("title") or "").strip())
        fuente_el = item.find("source")
        fuente = (fuente_el.text or "").strip() if fuente_el is not None else ""
        if fuente:
            titulo = re.sub(r"\s+-\s+" + re.escape(fuente) + r"\s*$", "", titulo)
        try:
            fecha = parsedate_to_datetime((item.findtext("pubDate") or "").strip()).date()
        except (TypeError, ValueError):
            continue
        if (hoy - fecha).days > PRENSA_DIAS or fecha > hoy:
            continue
        t = normalizar(titulo)
        if PRENSA_RUIDO.search(t):
            continue
        ponente, tema = analizar_laureado(titulo, "", laureados)
        laureado = ponente or tema
        hay_premio = bool(PRENSA_PREMIO.search(t)) or bool(laureado)
        # Hace falta: un premio o laureado, algo de Sevilla y una acción (visita, conferencia...) en el titular
        if not (hay_premio and PRENSA_LOCAL.search(t) and PRENSA_ACCION.search(t)):
            continue
        pistas.append({"titulo": titulo, "fuente": fuente or None, "fecha": fecha.strftime("%Y-%m-%d"),
                       "url": (item.findtext("link") or "").strip() or None, "laureado": laureado})
    return pistas


def pistas_prensa(hoy, laureados):
    """Recorre las consultas de prensa, quita repetidas y devuelve las más recientes."""
    todas, fallos = [], 0
    for consulta in PRENSA_CONSULTAS:
        url = "https://news.google.com/rss/search?q=" + quote_plus(consulta) + "&hl=es&gl=ES&ceid=ES:es"
        try:
            todas.extend(pistas_desde_rss(descargar(url), hoy, laureados))
        except Exception:
            fallos += 1
        _pausa()
    if fallos == len(PRENSA_CONSULTAS):
        raise ValueError("no se pudo leer Google Noticias")
    vistas, resultado = set(), []
    for p in sorted(todas, key=lambda p: p["fecha"], reverse=True):
        clave = normalizar(p["titulo"])[:60]
        if clave not in vistas:
            vistas.add(clave)
            resultado.append(p)
    return resultado[:PRENSA_MAXIMO]


LECTORES_WEB = [
    (NOMBRE_DIVULGAUS, eventos_divulgaus),
    (NOMBRE_IBIS, eventos_ibis),
    (NOMBRE_FISICA, eventos_fisica),
    (NOMBRE_CAJASOL, eventos_cajasol),
]


def completar_fichas_upo(crudos, hoy, limite=30):
    """Los eventos de la UPO (ICS) solo traen título: se abre su ficha para leer la descripción."""
    abiertas = 0
    for ev in crudos:
        if abiertas >= limite or (ev["fin"] or ev["inicio"]).date() < hoy or not ev["url"].startswith("http"):
            continue
        try:
            pagina = descargar(ev["url"].replace("http://", "https://"))
        except Exception:
            continue
        abiertas += 1
        m = re.search(r'<li class="ag_description">(.*?)</li>', pagina, re.S)
        if m:
            ev["descripcion"] = limpiar_html_parrafos(m.group(1))
        _pausa()


# ----------------------------------------------------------------------------
# Programa principal
# ----------------------------------------------------------------------------
PALABRAS_COMUNES_CHARLA = PALABRAS_COMUNES | {
    "charla", "charlas", "conferencia", "conferencias", "ciclo", "seminario", "jornada", "coloquio",
    "divulgativa", "divulgativas", "universidad", "sevilla", "facultad", "ciencia", "ciencias",
}


def _mismo_evento(a, b):
    """¿Son la misma charla publicada en dos webs distintas? (mismo día y títulos parecidos)"""
    if a["fecha"] != b["fecha"]:
        return False
    ca = claves_titulo(a["titulo"], PALABRAS_COMUNES_CHARLA)
    cb = claves_titulo(b["titulo"], PALABRAS_COMUNES_CHARLA)
    if not ca or not cb:
        return False
    comunes = len(ca & cb)
    return comunes >= 2 and comunes >= 0.6 * min(len(ca), len(cb))


def _anadir_sin_duplicar(lista, ev):
    """Añade el evento a la lista salvo que ya esté (mismo id o misma charla en otra web).
    Devuelve 1 si lo añade y 0 si lo funde con uno existente."""
    for viejo in lista:
        if viejo["id"] == ev["id"] or (viejo["tipo"] == ev["tipo"] == "charla" and _mismo_evento(viejo, ev)):
            if viejo["id"] != ev["id"]:
                viejo.setdefault("otrosIds", []).append(ev["id"])
            if ev.get("destacado") and not viejo.get("destacado"):
                viejo["destacado"], viejo["laureado"] = True, ev.get("laureado")
            if ev.get("laureadoTema") and not viejo.get("laureadoTema"):
                viejo["laureadoTema"] = ev["laureadoTema"]
            viejo["mencionaNobel"] = bool(viejo.get("mencionaNobel") or ev.get("mencionaNobel"))
            for campo in ("hora", "lugar"):
                if not viejo.get(campo) and ev.get(campo):
                    viejo[campo] = ev[campo]
            if ev["fuente"] not in viejo["fuente"].split(" + "):
                viejo["fuente"] += " + " + ev["fuente"]
            return 0
    lista.append(ev)
    return 1


def cargar_json_anterior():
    """Lo que había en eventos.json la vez anterior (o {} si no existe o está roto)."""
    try:
        with open(SALIDA, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def _aviso_certificados(error):
    if "CERTIFICATE_VERIFY_FAILED" in str(error):
        print("        -> Problema de certificados de tu PC. Ejecuta:  pip install truststore")


def recolectar(mostrar_descartados=False, forzar_laureados=False):
    hoy = hoy_madrid()
    anterior = cargar_json_anterior()
    anteriores = anterior.get("eventos", [])
    try:
        datos = actualizar_laureados_nobel(forzar_laureados)
        print(f"[OK] Lista oficial de Nobel: {len(datos['laureados'])} laureados vivos (del {datos['actualizado'][:10]})")
    except Exception as e:
        print(f"[AVISO] No se pudo actualizar la lista de Nobel ({str(e)[:80]}); uso la que ya tengo")
        _aviso_certificados(e)
    laureados = cargar_laureados()
    aceptados, fallidas, fuentes_ok = [], [], 0

    def procesar(nombre, crudos):
        buenos, descartados = 0, []
        for ev in crudos:
            ev.setdefault("fuente", nombre)
            final, motivo = clasificar(ev, laureados, hoy)
            if final:
                buenos += _anadir_sin_duplicar(aceptados, final)
            elif motivo and motivo != "ya pasado":
                descartados.append((ev["titulo"], motivo))
        print(f"[OK] {nombre}: {len(crudos)} eventos leídos, {buenos} charlas guardadas")
        if mostrar_descartados:
            for titulo, motivo in descartados:
                print(f"       descartado ({motivo}): {titulo[:80]}")

    # 1) Charlas: eventos de la UPO y de la US (ICS / RSS)
    for codigo, lector, nombre, url in FUENTES:
        try:
            texto = descargar(url)
            crudos = eventos_desde_ics(codigo, texto) if lector == "ics" else eventos_desde_rss(codigo, texto)
            for ev in crudos:
                ev["fuente"] = nombre
            if codigo == "upo":
                completar_fichas_upo(crudos, hoy)
        except Exception as e:  # una fuente caída no debe tumbar a las demás
            print(f"[FALLO] {nombre}: {e}")
            _aviso_certificados(e)
            fallidas.append(nombre)
            continue
        fuentes_ok += 1
        procesar(nombre, crudos)

    # 2) Charlas: webs de divulgación, IBiS, Física y Cajasol
    for nombre, lector in LECTORES_WEB:
        try:
            crudos = lector(hoy)
        except Exception as e:
            print(f"[FALLO] {nombre}: {e}")
            _aviso_certificados(e)
            fallidas.append(nombre)
            continue
        fuentes_ok += 1
        procesar(nombre, crudos)

    num_charlas = len(aceptados)

    # 3) Torneos de ajedrez
    torneos, torneos_ok, torneos_fallidos = recolectar_torneos(hoy)
    fuentes_ok += torneos_ok
    fallidas.extend(torneos_fallidos)
    for t in sorted(torneos, key=lambda e: e["fecha"]):
        _anadir_sin_duplicar(aceptados, t)
    print(f"     {len(torneos)} torneos guardados")
    for t in sorted(torneos, key=lambda e: e["fecha"]):
        print(f"       {t['fecha']}  {t['titulo'][:58]:58}  federación: {t['federacion']}")

    # 4) Prensa: pistas de visitas de laureados
    try:
        pistas = pistas_prensa(hoy, laureados)
        print(f"[OK] Prensa (Google Noticias): {len(pistas)} pistas")
    except Exception as e:
        pistas = anterior.get("pistas", [])     # si falla, se dejan las de la vez anterior
        print(f"[FALLO] Prensa (Google Noticias): {e}")
        _aviso_certificados(e)

    if fuentes_ok == 0:
        print("No se pudo leer ninguna fuente; no toco eventos.json")
        return 1

    # Si una fuente falla, se conservan sus eventos de la vez anterior (los que aún no han pasado)
    conservados = 0
    ids = {e["id"] for e in aceptados}
    for ev in anteriores:
        fuentes_ev = [x.strip() for x in ev.get("fuente", "").split(" + ")]
        if (ev["id"] not in ids and any(n in fuentes_ev for n in fallidas)
                and (ev.get("fechaFin") or ev["fecha"]) >= hoy.isoformat()):
            aceptados.append(ev)
            conservados += 1
    if conservados:
        print(f"[AVISO] {conservados} eventos de la vez anterior se conservan porque su fuente falló hoy")

    aceptados.sort(key=lambda e: (e["fecha"], e["hora"] or ""))
    contenido = {
        "generado": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "total": len(aceptados),
        "eventos": aceptados,
        "pistas": pistas,
    }
    with open(SALIDA, "w", encoding="utf-8") as f:
        json.dump(contenido, f, ensure_ascii=False, indent=1)
    charlas = [e for e in aceptados if e["tipo"] == "charla"]
    destacadas = [e for e in charlas if e["destacado"]]
    suaves = [e for e in charlas if not e["destacado"] and (e.get("laureadoTema") or e.get("mencionaNobel"))]
    for e in destacadas:
        print(f"   [DESTACADA] {e['fecha']}  {e['titulo'][:60]}  -> {e['laureado']}")
    for e in suaves:
        print(f"   [menciona Nobel] {e['fecha']}  {e['titulo'][:60]}  -> {e.get('laureadoTema') or ''}")
    for p in pistas:
        print(f"   [prensa] {p['fecha']}  {p['titulo'][:80]}  ({p['fuente']})")
    print(f"\nListo: {len(charlas)} charlas ({len(destacadas)} destacadas), {len(aceptados) - len(charlas)} "
          f"torneos y {len(pistas)} pistas de prensa guardados en {SALIDA.name}")
    return 0


def prueba():
    """Comprobaciones rápidas de que los filtros y los lectores se comportan como deben (sin internet)."""
    laureados = cargar_laureados()
    hoy = date(2026, 11, 12)
    base = {"fin": None, "con_hora": True, "url": "", "descripcion": "", "fuente": "prueba",
            "inicio": datetime(2026, 12, 1, 12, 0), "lugar": "Facultad de Física, Sevilla"}

    def caso(titulo, **extra):
        ev = dict(base, id="x-1", titulo=titulo, **extra)
        return clasificar(ev, laureados, hoy)

    fallos = 0

    def comprobar(nombre, condicion):
        nonlocal fallos
        print(("  OK   " if condicion else "  FALLA ") + nombre)
        fallos += 0 if condicion else 1

    print("Filtros de charlas")
    r, _ = caso("Conferencia de Takaaki Kajita sobre neutrinos")
    comprobar("laureado conocido como ponente -> destacado", bool(r and r["destacado"]))
    r, _ = caso("Charla sobre neutrinos de Takaaki Kajita")
    comprobar("laureado al final del título, sin otras pistas -> destacado", bool(r and r["destacado"]))
    r, _ = caso("Charla: las mates del Nobel de Física 2024 explicadas")
    comprobar("menciona Nobel pero sin laureado -> no destacado, sí marca suave",
              bool(r and not r["destacado"] and r["mencionaNobel"]))
    r, _ = caso("Charla de John Clarke sobre cocina")
    comprobar("nombre común sin contexto de premio -> no destacado", bool(r and not r["destacado"]))
    r, _ = caso("Charla de John Clarke, Premio Nobel de Física")
    comprobar("nombre común con contexto de premio -> destacado", bool(r and r["destacado"]))
    r, _ = caso("Charla sobre el Nobel de Física 2025 de Takaaki Kajita",
                descripcion="La charla corre a cargo de la profesora Ana Pérez, de la Universidad de Sevilla.")
    comprobar("el laureado es el tema y da la charla otra persona -> no destacado, sí tema",
              bool(r and not r["destacado"] and r["laureadoTema"]))
    r, m = caso("Mercado Agroecológico La Ilustración")
    comprobar("mercado -> descartado", r is None)
    r, m = caso("Taller de observación astronómica")
    comprobar("taller -> descartado", r is None)
    r, m = caso("Conferencia de inicio de curso: Juan García-Bellido en la Facultad de Física")
    comprobar("'inicio de curso' no cuenta como curso -> se guarda", r is not None)
    r, m = caso("Curso de verano de matemáticas")
    comprobar("curso de verdad -> descartado", r is None)
    r, m = caso("Conferencia sobre historia", lugar="Calle Alameda Vieja, Jerez de la Frontera")
    comprobar("charla en Jerez -> descartada por lugar", r is None and m == "fuera de Sevilla")
    r, m = caso("Conferencia antigua", inicio=datetime(2026, 1, 1, 12, 0))
    comprobar("evento pasado -> descartado", r is None and m == "ya pasado")
    r, _ = caso("Charla coloquio del proyecto InmigrARTE")
    comprobar("charla normal -> guardada", r is not None and not r["destacado"])
    r, _ = caso("Actividad de las Semanas de la Ciencia", usar_descripcion=True,
                descripcion="La investigadora Paula Villalba ofrece la charla 'El río', el jueves a las 11.00 horas")
    comprobar("charla anunciada solo en la descripción -> guardada", r is not None)
    r, _ = caso("Actividad de las Semanas de la Ciencia", descripcion="ofrece la charla 'El río'")
    comprobar("sin 'usar_descripcion' el título manda -> descartada", r is None)
    r, _ = caso("Seminario del área de neurociencias", es_charla=False)
    comprobar("es_charla=False manda sobre el título", r is None)
    comprobar("hora invierno (UTC+1)", utc_a_madrid(datetime(2026, 11, 12, 11, 0, tzinfo=timezone.utc)).hour == 12)
    comprobar("hora verano (UTC+2)", utc_a_madrid(datetime(2026, 7, 15, 10, 0, tzinfo=timezone.utc)).hour == 12)

    print("Laureados: ¿quién da la charla y de quién se habla?")
    lista = _patrones_laureados([
        {"nombre": "Francis Halzen", "premio": "Nobel de Física 2026", "ambiguo": False},
        {"nombre": "Morten Meldal", "premio": "Nobel de Química 2022", "ambiguo": False,
         "alias": ["Morten Peter Meldal"]},
    ])
    halzen = ("La Facultad de Física continúa con su ya tradicional ciclo de conferencias dedicadas al Premio Nobel "
              "de Física. En esta edición, la charla estará centrada en el Premio Nobel de Física 2026, concedido a "
              "Francis Halzen por su papel fundamental en el desarrollo de la astronomía de neutrinos de alta "
              "energía y la creación del observatorio IceCube, una infraestructura científica que ha abierto una "
              "nueva ventana para explorar el Universo. | La conferencia, titulada “NEUTRINO: El mensajero del "
              "Universo”, será impartida por el Prof. Juan Antonio Caballero, catedrático del Departamento de "
              "Física Atómica, Molecular y Nuclear de la Universidad de Sevilla. | Lugar: Aula Magna | Resumen | "
              "Francis Halzen impulsó una idea revolucionaria: utilizar el hielo antártico como detector gigante "
              "de neutrinos. | Ponente | Juan Antonio Caballero es catedrático de universidad.")
    p, t = analizar_laureado("Francis Halzen: Premio Nobel de Física 2026. NEUTRINO: El mensajero del Universo",
                             halzen, lista)
    comprobar("Halzen (charla de un profesor local sobre su Nobel) -> tema, no ponente",
              p is None and t and "Halzen" in t)
    p, t = analizar_laureado("Morten Peter Meldal, Premio Nobel de Química 2022, ofrece una conferencia en la US", "", lista)
    comprobar("'X, Nobel, ofrece una conferencia' -> ponente (también con el nombre completo)",
              p and "Meldal" in p and t is None)
    p, t = analizar_laureado("Morten Peter Meldal, Nobel de Química, ofrece una charla", "", _patrones_laureados([
        {"nombre": "Morten Meldal", "premio": "Nobel de Química 2022", "ambiguo": False}]))
    comprobar("el nombre sin segundo nombre también vale con segundo nombre", p and "Meldal" in p)
    p, t = analizar_laureado("Conferencia magistral", "Impartida por Morten Meldal, Premio Nobel de Química.", lista)
    comprobar("'impartida por X' -> ponente", p and "Meldal" in p)
    p, t = analizar_laureado("Charla sobre el Nobel de Química de Morten Meldal, a cargo de Ana Pérez", "", lista)
    comprobar("'sobre el Nobel de X, a cargo de otra persona' -> tema", p is None and t and "Meldal" in t)
    p, t = analizar_laureado("Jornada de química", "En ediciones anteriores participaron Morten Meldal y otros.", lista)
    comprobar("mención de pasada en la descripción -> tema", p is None and t and "Meldal" in t)

    larga = "ciclo-de-charlas-divulgativas-sobre-el-ictus-para-el-alumnado-universitario-con-un-titulo-larguisimo"
    comprobar("los identificadores largos no se confunden entre sí",
              _slug("/eventos/" + larga + "-2") != _slug("/eventos/" + larga + "-3")
              and _slug("/eventos/" + larga + "-2") == _slug("/eventos/" + larga + "-2/"))
    print("Fecha, hora y lugar dentro de un texto")
    f, h, l = extraer_fecha_hora_lugar(
        "Lugar : Aula Magna, Facultad de Física, Avda. Reina Mercedes s/n, Sevilla. | Cuándo : Jueves 12 de noviembre "
        "a las 12:00. | Resumen | El neutrino es...", hoy)
    comprobar("Física: 'Lugar / Cuándo'", f == date(2026, 11, 12) and h == "12:00"
              and l == "Aula Magna, Facultad de Física, Avda. Reina Mercedes s/n, Sevilla")
    f, h, l = extraer_fecha_hora_lugar(
        "Ponente : José Miguel Viñas | Fecha : 15 de octubre de 2026 Hora : 12:00 h Lugar : Aula Magna de la "
        "Facultad de Física, Universidad de Sevilla | Entrada libre hasta completar aforo.", hoy)
    comprobar("Física: 'Fecha / Hora / Lugar' en párrafos", f == date(2026, 10, 15) and h == "12:00"
              and l == "Aula Magna de la Facultad de Física, Universidad de Sevilla")
    f, h, l = extraer_fecha_hora_lugar(
        "La investigadora ofrece la charla 'Herramientas' el martes 10 de noviembre a las 11.00 horas en el Salón de "
        "Grados de la Facultad de Ciencias de la Educación de la US. | Charla divulgativa sobre...", hoy)
    comprobar("DivulgaUS: 'a las 11.00 horas en el ...'", h == "11:00"
              and l == "Salón de Grados de la Facultad de Ciencias de la Educación de la US")
    f, h, l = extraer_fecha_hora_lugar("Día: sábado, 14 de noviembre | Hora: 16:30 horas. | Lugar: Sala Antonio "
                                       "Machado (C/Chicarreros, 1) | Entradas en taquilla", hoy)
    comprobar("Cajasol: 'Día / Hora / Lugar'", f == date(2026, 11, 14) and h == "16:30"
              and l == "Sala Antonio Machado (C/Chicarreros, 1)")
    comprobar("hora 'a las 12 horas'", buscar_hora("se celebra a las 12 horas en el aula") == "12:00")
    comprobar("hora imposible no se acepta", buscar_hora("a las 27:99 horas") is None)

    print("Lectores de webs (sobre trozos de HTML reales)")
    semana = ('<div class="contents"><a href="/eventos/ciclo-de-charlas-ictus-2" hreflang="es">Ciclo de charlas '
              'divulgativas sobre el ictus</a>\n<time datetime="2026-11-30T11:30:00Z" class="datetime">Lun, '
              '30/11/2026 - 12:30</time></div><div class="contents"><a href="/eventos/congreso-x" hreflang="es">'
              'Congreso Internacional &#039;La corte&#039;</a><time datetime="2026-11-05T10:42:57Z" '
              'class="datetime">Jue, 05/11/2026 - 11:42</time></div>')
    s = parsear_semana_divulgaus(semana)
    comprobar("DivulgaUS: lee título, hora de Madrid y marca las horas falsas",
              len(s) == 2 and s[0][2] == datetime(2026, 11, 30, 12, 30) and s[0][3] is True
              and s[1][1] == "Congreso Internacional 'La corte'" and s[1][3] is False)
    ficha = ('<article><div class="node__content"><div class="field"><h3 class="field__label">Fecha evento</h3>'
             '<time datetime="2026-11-10T10:00:00Z" class="datetime">Mar, 10/11/2026 - 11:00</time></div>'
             '<div class="field__item">Esta actividad se celebra el martes 10 de noviembre</div>'
             '<div class="field__item"><p>Charla divulgativa sobre herramientas.</p></div></div></article>')
    comprobar("DivulgaUS: texto de la ficha sin la fecha de cabecera",
              parsear_ficha_divulgaus(ficha).startswith("Esta actividad se celebra"))
    ibis = ('<article class="event-itemlist"><div class="row"><div class="col-auto"><time class="time-box">'
            '<strong>17</strong><span>Nov</span><strong>26</strong></time></div><div class="col">'
            '<h5 class="event-itemlist--title"><a href="/es/eventos/2026/11/proyecto-elara/"><p>Proyecto ELARA: '
            'genómica</p></a></h5></div></div></article>')
    comprobar("IBiS: lee el listado", parsear_listado_ibis(ibis) == [("/es/eventos/2026/11/proyecto-elara/",
                                                                      "Proyecto ELARA: genómica")])
    ficha_ibis = ('<ol><li class="breadcrumb-item"><a href="/es/eventos/">Eventos</a></li><li class="breadcrumb-item">'
                  '<a href="/es/eventos/seminarios/">Seminarios del Área de Neurociencias</a></li></ol><table><tbody>'
                  '<tr><th class="align-middle">Fecha <a href="x"><span>event</span></a></th><td class="align-middle">'
                  '17/11/2026 08:15 &rarr; 17/11/2026 09:30</td></tr><tr><th>Lugar</th><td><p>SALÓN DE ACTOS IBiS</p>'
                  '</td></tr><tr><th>Ponentes</th><td><p><strong>GUILLERMO MARTÍN</strong></p></td></tr></tbody></table>')
    fi = parsear_ficha_ibis(ficha_ibis)
    comprobar("IBiS: lee fecha, lugar, ponentes y categoría",
              fi["inicio"] == datetime(2026, 11, 17, 8, 15) and fi["fin"] == datetime(2026, 11, 17, 9, 30)
              and fi["lugar"] == "SALÓN DE ACTOS IBiS" and fi["ponentes"] == "GUILLERMO MARTÍN"
              and fi["categoria"] == "Seminarios del Área de Neurociencias")
    comprobar("IBiS: un seminario con ponente es charla", es_charla_ibis("Illuminating visual circuits", fi))
    comprobar("IBiS: un 'consortium meeting' no es charla",
              not es_charla_ibis("VOLABIOS CONSORTIUM MEETING", dict(fi, categoria="Otros")))
    fisica = ('<div class="noticias__texto-fecha"><time datetime="2026-11-12T12:00:00Z" class="datetime">Jue, '
              '12/11/2026</time>\n</div>\n        <h4 class="noticias__texto-titulo"><a href="/noticias/francis-halzen" '
              'target="_blank">Francis Halzen: Premio Nobel de Física 2026</a></h4>')
    comprobar("Física: lee el listado", parsear_listado_fisica(fisica) == [
        (date(2026, 11, 12), "/noticias/francis-halzen", "Francis Halzen: Premio Nobel de Física 2026")])
    caja_a = ('<a href="https://fundacioncajasol.com/evento/anclaje/" class="event-item"><div class="col date-col">'
              '<span class="date h3"><span class="text-light">14 NOV</span>16:30</span></div><div class="col '
              'place-col"><span class="place h3 text-light">SEVILLA</span></div><div class="col title-col">'
              '<div class="title-holder"><span class="subtitle h6">ENCUENTRO</span><span class="title h3">ANCLAJE: '
              'ADICCIÓN Y JUVENTUD</span><span class="title h4"></span></div></div></a>')
    caja_b = caja_a.replace("14 NOV</span>16:30", "14 SEP</span>14 DIC").replace("anclaje", "curso")
    caja_c = caja_a.replace("SEVILLA", "CÁDIZ").replace("anclaje", "cadiz")
    caja_d = caja_a.replace("14 NOV</span>16:30", "2 ENE</span>").replace("anclaje", "enero")
    lc = parsear_listado_cajasol(caja_a + caja_a + caja_b + caja_c + caja_d, hoy)
    comprobar("Cajasol: sin repetidos y solo Sevilla", len(lc) == 3)
    comprobar("Cajasol: fecha con hora", lc[0]["ini"] == date(2026, 11, 14) and lc[0]["hora"] == "16:30")
    comprobar("Cajasol: rango de fechas", lc[1]["ini"] == date(2026, 9, 14) and lc[1]["fin"] == date(2026, 12, 14))
    comprobar("Cajasol: enero sin año -> año siguiente", lc[2]["ini"] == date(2027, 1, 2))
    comprobar("Cajasol: título y tipo", lc[0]["titulo"] == "ANCLAJE: ADICCIÓN Y JUVENTUD" and lc[0]["tipo"] == "ENCUENTRO")

    print("Prensa")
    rss = ('<rss><channel><item><title>El alcalde de Sevilla recibe al Nobel de Química Morten Meldal en el '
           'Ayuntamiento - ABC</title><link>https://news.google.com/rss/articles/x</link><pubDate>Fri, 16 Oct 2026 '
           '07:00:00 GMT</pubDate><source url="https://abc.es">ABC</source></item>'
           '<item><title>La canadiense Anne Carson, Premio Nobel de Literatura 2026 - Diario de Sevilla</title>'
           '<link>https://news.google.com/rss/articles/y</link><pubDate>Thu, 08 Oct 2026 07:00:00 GMT</pubDate>'
           '<source url="https://x.es">Diario de Sevilla</source></item>'
           '<item><title>Ernesto Carmona: "Ojalá tengamos otro Nobel español" - ABC</title><link>z</link>'
           '<pubDate>Sun, 04 Oct 2026 07:00:00 GMT</pubDate><source url="https://abc.es">ABC</source></item>'
           '<item><title>El cicCartuja acoge la visita de Morten P. Meldal, premio Nobel de Química 2022 - Diario de '
           'Sevilla</title><link>v</link><pubDate>Mon, 12 Oct 2026 07:00:00 GMT</pubDate><source url="https://d.es">'
           'Diario de Sevilla</source></item>'
           '<item><title>El enigma de las moléculas zurdas que resolvieron Henri B. Kagan y Kenso Soai - ABC</title>'
           '<link>u</link><pubDate>Mon, 12 Oct 2026 07:00:00 GMT</pubDate><source url="https://abc.es">ABC</source></item>'
           '<item><title>Un premio Nobel ofrece una conferencia en la US - Universidad de Sevilla</title><link>w</link>'
           '<pubDate>Wed, 30 Sep 2026 11:26:40 GMT</pubDate><source url="https://us.es">Universidad de Sevilla'
           '</source></item></channel></rss>')
    ps = pistas_desde_rss(rss, hoy, lista)
    comprobar("Prensa: se queda con visitas de laureados a Sevilla; quita Literatura, ruido y artículos sin visita",
              len(ps) == 3 and ps[0]["laureado"] and "Meldal" in ps[0]["laureado"]
              and ps[1]["laureado"] and "Meldal" in ps[1]["laureado"] and ps[2]["laureado"] is None)

    print("Torneos")
    h = date(2026, 11, 12)
    comprobar("fecha simple sin año", parsear_fechas("14 Noviembre", h) == (date(2026, 11, 14), None))
    comprobar("rango sin año", parsear_fechas("11-13 diciembre", h) == (date(2026, 12, 11), date(2026, 12, 13)))
    comprobar("rango con año", parsear_fechas("8-16 Enero 2027", h) == (date(2027, 1, 8), date(2027, 1, 16)))
    comprobar("enero sin año -> año siguiente", parsear_fechas("17 Enero", h) == (date(2027, 1, 17), None))
    comprobar("rango entre meses", parsear_fechas("30 Noviembre - 2 Diciembre", h) == (date(2026, 11, 30), date(2026, 12, 2)))
    comprobar("federación: 'federados o no' -> libre",
              detectar_federacion("Pueden participar todos, ESTÉN FEDERADOS O NO.")[0] == "libre")
    comprobar("federación: no federados pagan suplemento -> libre",
              detectar_federacion("Los jugadores no federados deberán abonar un suplemento de 2€.")[0] == "libre")
    comprobar("federación: aficionados y federados -> libre",
              detectar_federacion("Podrán participar todos los jugadores aficionados y federados.")[0] == "libre")
    comprobar("federación: solo federados -> exige",
              detectar_federacion("Podrán participar únicamente jugadores federados.")[0] == "exige")
    comprobar("federación: 'federados registrados en gefe' -> exige",
              detectar_federacion("Podrán jugar todos los participantes federados que están registrados en gefe.net.")[0] == "exige")
    comprobar("federación: no se admiten no federados -> exige",
              detectar_federacion("No se admitirán jugadores no federados.")[0] == "exige")
    comprobar("federación: sin mención -> sin_confirmar",
              detectar_federacion("El torneo se juega a 7 rondas suizo.")[0] == "sin_confirmar")
    a = {"titulo": 'II Torneo "Aljarasol"', "ini": date(2026, 12, 20)}
    b = {"titulo": "II Abierto de Rápidas Aljarasol", "ini": date(2026, 12, 20)}
    c = {"titulo": 'XIV Olimpiada Interescolar "Diputación de Sevilla"', "ini": date(2027, 1, 9)}
    d = {"titulo": 'III Torneo Internacional Femenino "Diputación de Sevilla"', "ini": date(2027, 1, 9)}
    comprobar("mismo torneo en dos fuentes se empareja", _son_el_mismo(a, b))
    comprobar("torneos distintos el mismo día no se mezclan", not _son_el_mismo(c, d))

    print("Charlas repetidas en dos webs")
    e1 = {"id": "us-1", "tipo": "charla", "fecha": "2026-11-20", "titulo": "Conferencia: Los neutrinos y el Universo",
          "destacado": False, "mencionaNobel": False, "hora": None, "lugar": None, "fuente": "A"}
    e2 = dict(e1, id="div-9", titulo="Los neutrinos y el Universo (conferencia)", destacado=True,
              laureado="X (Nobel)", hora="12:00", fuente="B")
    e3 = dict(e1, id="div-10", titulo="Otra charla distinta sobre arte barroco")
    lista_e = []
    n = _anadir_sin_duplicar(lista_e, dict(e1)) + _anadir_sin_duplicar(lista_e, dict(e2)) \
        + _anadir_sin_duplicar(lista_e, dict(e3))
    comprobar("se funden las dos copias de la misma charla y no la distinta", n == 2 and len(lista_e) == 2)
    comprobar("la fusión conserva lo mejor de cada una",
              lista_e[0]["destacado"] and lista_e[0]["hora"] == "12:00" and lista_e[0]["otrosIds"] == ["div-9"]
              and lista_e[0]["fuente"] == "A + B")

    print("\nTodo correcto." if fallos == 0 else f"\n{fallos} comprobaciones fallan.")
    return 1 if fallos else 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="Recolector de charlas y torneos de Sevilla")
    ap.add_argument("--descartados", action="store_true", help="lista los eventos descartados")
    ap.add_argument("--prueba", action="store_true", help="ejecuta comprobaciones internas")
    ap.add_argument("--laureados", action="store_true", help="fuerza la actualización de la lista de Nobel")
    args = ap.parse_args()
    try:   # que un carácter raro (emoji, comillas) nunca haga fallar un print en la consola de Windows
        sys.stdout.reconfigure(errors="replace")
    except Exception:
        pass
    sys.exit(prueba() if args.prueba else recolectar(args.descartados, args.laureados))
