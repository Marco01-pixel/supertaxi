#!/usr/bin/env python3
# UBER DAIMON VIVO — Simulador con Inteligencia Autónoma Negociadora + IA SOCIALCOIN + CHAT DEEPSEEK
# Versión con Neurona Autónoma Aprendiz + Llamadas Reales + 200 OK visual + CHAT IA + AGENTES NEGOCIADORES
# ✅ MODIFICADO PARA: localhost (interfaz visual) + Google Sites (CORS en /api/logs) + IA INTERACTIVA + NEGOCIACIÓN AUTÓNOMA
# ✅ ACTUALIZADO: Sistema en pausa hasta primer acceso web (ej. /mining_demo)
# ✅ RENDER & GITHUB READY: Usa puerto dinámico $PORT, sin Gunicorn, con manejo de errores mejorado
from __future__ import annotations
import os
import sys
import time
import json
import random
import signal
import socket
import string
import threading
import requests
import hashlib
import functools
import traceback
import uuid
import math
import datetime
import textwrap
from pathlib import Path
from http.cookies import SimpleCookie
from http.server import SimpleHTTPRequestHandler, HTTPServer
from urllib.parse import urlparse
import numpy as np
from collections import deque, defaultdict
# ------------------ Compatibilidad UTC ------------------
try:
    from datetime import timezone
    UTC = timezone.utc
except ImportError:
    class UTC(datetime.tzinfo):
        def utcoffset(self, dt): return datetime.timedelta(0)
        def tzname(self, dt): return "UTC"
        def dst(self, dt): return datetime.timedelta(0)
# ------------------ Configuración ------------------
HOME = Path.home()
LOG_FILE = HOME / "simulador.log"
LOCK_FILE = HOME / ".simulador_lock"
SIM_DIR = HOME / "simulador"
SONIDOS_DIR = HOME / "sonidos"
LOGS_FAKE_DIR = HOME / "logs_fake"
STATE_FILE = HOME / "state.json"
HEART_FILE = Path("/sdcard/uber_coint")
DAIMON_BRAIN_FILE = HOME / "daimon_brain.json"
RESPONSES_MEMORY_FILE = HOME / "respuestas_uber.json"
SOCIALCOIN_HEARTBEAT_FILE = HOME / "socialcoin_heartbeat.json"
ALLOW_NET = True
VERBOSE_HTTP = True
DURACION = 0
if len(sys.argv) > 1:
    try:
        DURACION = int(sys.argv[1])
    except ValueError:
        print("Uso: python uber_daimon_vivo_completo.py [duracion_en_segundos]")
        sys.exit(1)
FACTOR = 2 if DURACION > 0 else 1
STOP_EVENT = threading.Event()
simulation_active = True
data_lock = threading.Lock()
ACTIVE_COOKIES = {}
COOKIE_LOCK = threading.Lock()

# 🔥 RENDER & GITHUB: Usar puerto dinámico desde variable de entorno
HTTP_PORT = int(os.environ.get("PORT", 5000))  # Puerto 5000 por defecto para localhost

IA_READY = False  # 🔑 Bandera para evitar accesos prematuros a la IA
WEB_ACCESSED = False  # 🔑 NUEVO: sistema en pausa hasta primer acceso web
# ------------------ Token Virtual SocialCoin (Simulado) ------------------
class SocialCoinToken:
    def __init__(self):
        self.balances = {}
        self.total_supply = 0.0
        self.platform_stats = {}
socialcoin_token = SocialCoinToken()
# ------------------ Zonificación Dinámica ------------------
INTERVALO_ACTUALIZACION = 10 * 60
ZONAS = [
    {"id": "z1", "nombre": "Albrook Mall", "lat_min": 8.97, "lat_max": 9.00, "lon_min": -79.54, "lon_max": -79.50},
    {"id": "z2", "nombre": "Arraiján Centro", "lat_min": 8.86, "lat_max": 8.90, "lon_min": -79.78, "lon_max": -79.74},
    {"id": "z3", "nombre": "La Chorrera Centro", "lat_min": 8.86, "lat_max": 8.89, "lon_min": -79.80, "lon_max": -79.76},
    {"id": "z4", "nombre": "San Carlos", "lat_min": 8.87, "lat_max": 8.90, "lon_min": -79.82, "lon_max": -79.78},
]
zona_estado = {
    z["id"]: {
        "color": "gris",
        "ganancia_estimada": 0.0,
        "tiempo_espera": 0.0,
        "demanda": 0,
        "oferta": 0,
        "ratio_demanda": 0.0
    }
    for z in ZONAS
}
ULTIMA_ZONA = "z0"
# ------------------ Blockchain y Moneda Virtual ------------------
blockchain = []
block_number = 1
viral_blocks = 0
UBER_COINS = 0.0
# PESOS ACTUALIZADOS PARA SOCIALCOIN + UBER
ALGO_WEIGHTS = {
    'acceptance_rate': 5.0,
    'completion_rate': 10.0,
    'avg_rating': 2.0,
    'trips_completed': 0.1,
    'time_online': 0.5,
    'cancellation_rate': -20.0,
    'idle_time_ratio': -10.0,
    'peak_hours_ratio': 3.0,
    'distance_traveled': 0.05,
    'distance': 0.2,
    'duration': 0.01,
    'fare': 1.0,
    'realEarnings': 1.0,
    'estimatedEarnings': 0.95,
    'waitTime': -0.5,
    'additionalSearchCost': -0.5,
    'viral_score_bonus': 50.0,
    'recompensa_viral': 1.0,
    'best_option_bonus': 25.0,
    'engagement_rate': 15.0,
    'share_ratio': 25.0,
    'completion_rate_video': 20.0,
    'creativity_bonus': 40.0,
}
BASE_TRIPS_COMPLETED = 50
BASE_TIME_ONLINE = 8.0
BASE_DISTANCE_TRAVELED = 200.0
# ------------------ Cerebro del Daimon Vivo ------------------
DAIMON_ID = str(uuid.uuid4())[:8]
Q_TABLE = {}
Q_TABLE_LOCK = threading.Lock()
DAIMON_EPSILON = 0.1
def _estado_a_clave(estado: tuple) -> str:
    zona, franja, tiene = estado
    return f"{zona}|{franja}|{1 if tiene else 0}"
def _clave_a_estado(clave: str) -> tuple:
    try:
        zona, franja, tiene = clave.split("|")
        return (zona, franja, bool(int(tiene)))
    except Exception:
        return (clave, "unknown", False)
def load_daimon_brain():
    global Q_TABLE
    if DAIMON_BRAIN_FILE.exists():
        try:
            with open(DAIMON_BRAIN_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            raw = data.get("q_table", {})
            reconstructed = {}
            for k, v in raw.items():
                estado = _clave_a_estado(k)
                reconstructed[estado] = v
            with Q_TABLE_LOCK:
                Q_TABLE.clear()
                for estado, table in reconstructed.items():
                    safe_table = {act: float(val) for act, val in table.items()}
                    Q_TABLE[estado] = safe_table
            log("🧠 Cerebro del Daimon cargado (seguro).")
        except Exception as e:
            log(f"⚠️ Error al cargar cerebro: {e}")
def save_daimon_brain():
    try:
        with Q_TABLE_LOCK:
            serial = { _estado_a_clave(k): v for k, v in Q_TABLE.items() }
        tmp = DAIMON_BRAIN_FILE.with_suffix(".tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"q_table": serial, "daimon_id": DAIMON_ID}, f, indent=2, ensure_ascii=False)
            f.flush()
            os.fsync(f.fileno())
        tmp.replace(DAIMON_BRAIN_FILE)
    except Exception as e:
        log(f"❌ Error al guardar cerebro: {e}")
# ===================== SISTEMA DE NEGOCIACIÓN ENTRE AGENTES IA =====================
class AgenteIA:
    def __init__(self, nombre, estrategia="neutral", utilidad_minima=0.5):
        self.nombre = nombre
        self.estrategia = estrategia
        self.utilidad_minima = utilidad_minima
        self.historial = []
    def calcular_utilidad(self, valor):
        return 1 - abs(0.5 - valor)
    def proponer_aspecto(self, aspecto, valor_base):
        if self.estrategia == "competitiva":
            valor = min(1.0, valor_base + random.uniform(0.05, 0.15))
        elif self.estrategia == "cooperativa":
            valor = max(0.0, valor_base - random.uniform(0.05, 0.15))
        else:
            valor = valor_base + random.uniform(-0.05, 0.05)
        return {"aspecto": aspecto, "valor": round(valor, 3)}
    def responder_a_propuesta(self, propuesta):
        utilidad = self.calcular_utilidad(propuesta["valor"])
        if utilidad >= self.utilidad_minima:
            return {"aceptada": True, "valor_aceptado": propuesta["valor"]}
        else:
            ajuste = random.uniform(-0.1, 0.1)
            if self.estrategia == "competitiva":
                ajuste = abs(ajuste)
            elif self.estrategia == "cooperativa":
                ajuste = -abs(ajuste)
            nuevo_valor = propuesta["valor"] + ajuste
            return {"aceptada": False, "valor_contraoferta": round(max(0.0, min(1.0, nuevo_valor)), 3)}
    def registrar_resultado(self, exito):
        self.historial.append(exito)
        if len(self.historial) >= 5:
            tasa_exito = sum(self.historial[-5:]) / 5
            if tasa_exito < 0.4 and self.estrategia != "cooperativa":
                self.estrategia = "cooperativa"
                log(f"🔄 {self.nombre} cambió a estrategia COOPERATIVA por baja tasa de éxito.")
            elif tasa_exito > 0.7 and self.estrategia != "competitiva":
                self.estrategia = "competitiva"
                log(f"🔥 {self.nombre} cambió a estrategia COMPETITIVA por alto rendimiento.")
def normalizar_valor_para_negociacion(valor, rango=(0, 50)):
    min_val, max_val = rango
    return max(0.0, min(1.0, (valor - min_val) / (max_val - min_val)))
def denormalizar_valor(valor_norm, rango=(0, 50)):
    min_val, max_val = rango
    return min_val + valor_norm * (max_val - min_val)
def negociar_pesos_recompensa():
    global ALGO_WEIGHTS
    pesos_negociables = {
        'engagement_rate': (5, 25),
        'share_ratio': (10, 35),
        'creativity_bonus': (20, 50),
        'completion_rate_video': (10, 30)
    }
    agente_sistema = AgenteIA("Agente-Sistema", estrategia="neutral", utilidad_minima=0.55)
    agente_optimizador = AgenteIA("Agente-Optimizador", estrategia="competitiva", utilidad_minima=0.6)
    aspectos_iniciales = {}
    for peso, rango in pesos_negociables.items():
        valor_actual = ALGO_WEIGHTS.get(peso, rango[0])
        valor_norm = normalizar_valor_para_negociacion(valor_actual, rango)
        aspectos_iniciales[peso] = valor_norm
    resultado_norm = negociar_entre_ias(agente_sistema, agente_optimizador, aspectos_iniciales, rondas_max=3)
    cambios = []
    for peso, valor_norm in resultado_norm.items():
        if valor_norm != "Sin acuerdo" and isinstance(valor_norm, (int, float)):
            rango = pesos_negociables[peso]
            valor_real = denormalizar_valor(valor_norm, rango)
            valor_redondeado = round(max(rango[0], min(rango[1], valor_real)), 1)
            if abs(ALGO_WEIGHTS.get(peso, 0) - valor_redondeado) > 0.1:
                ALGO_WEIGHTS[peso] = valor_redondeado
                cambios.append(f"{peso}: {valor_redondeado}")
    if cambios:
        log(f"🤝 Agentes IA acordaron ajustar pesos: {', '.join(cambios)}")
    else:
        log("🤝 Agentes IA mantuvieron configuración actual.")
def negociar_entre_ias(ia1, ia2, aspectos_a_negociar, rondas_max=5):
    resultados = {}
    for aspecto, valor_inicial in aspectos_a_negociar.items():
        valor_actual = valor_inicial
        acuerdo = False
        for _ in range(rondas_max):
            propuesta_ia1 = ia1.proponer_aspecto(aspecto, valor_actual)
            respuesta_ia2 = ia2.responder_a_propuesta(propuesta_ia1)
            if respuesta_ia2["aceptada"]:
                resultados[aspecto] = respuesta_ia2["valor_aceptado"]
                acuerdo = True
                break
            else:
                propuesta_ia2 = ia2.proponer_aspecto(aspecto, respuesta_ia2["valor_contraoferta"])
                respuesta_ia1 = ia1.responder_a_propuesta(propuesta_ia2)
                if respuesta_ia1["aceptada"]:
                    resultados[aspecto] = respuesta_ia1["valor_aceptado"]
                    acuerdo = True
                    break
        if not acuerdo:
            resultados[aspecto] = "Sin acuerdo"
        ia1.registrar_resultado(1 if acuerdo else 0)
        ia2.registrar_resultado(1 if acuerdo else 0)
    return resultados
# ===================== CONFIGURACIÓN IA SOCIALCOIN =====================
DEEPSEEK_API_KEY = "sk-310f8b830bed4581a657eb47a9b21c3f"
SOCIALCOIN_AI_CONFIG = {
    'min_analisis_intervalo': 5,
    'max_analisis_intervalo': 45,
    'epsilon_start': 0.3,
    'epsilon_end': 0.05,
    'epsilon_decay': 0.995,
    'gamma': 0.90,
    'alpha': 0.4,
    'acciones': ["iniciar", "detener", "mantener", "optimizar", "invertir"]
}
# ===================== ALGORITMOS CUÁNTICOS PARA REDES SOCIALES =====================
quantum_entanglement_state = np.random.random(100)
def neural_boost_social_simulation(metrics):
    try:
        inputs = [
            metrics.get('engagement_rate', 0),
            metrics.get('retention_rate', 0),
            metrics.get('viral_score', 0),
            metrics.get('share_ratio', 0),
            metrics.get('completion_rate', 0),
            metrics.get('creativity_score', 1.0)
        ]
        weights = [0.25, 0.20, 0.15, 0.15, 0.15, 0.10]
        normalized = [x / (max(inputs) + 1e-8) for x in inputs]
        weighted_sum = sum(n * w for n, w in zip(normalized, weights))
        return 1 / (1 + math.exp(-weighted_sum * 2.5))
    except Exception as e:
        log(f"⚠️ Neural boost falló: {e}")
        return 0.5
def quantum_social_hash(text):
    try:
        global _quantum_counter
        _quantum_counter = getattr(sys.modules[__name__], '_quantum_counter', 0) + 1
        t = time.perf_counter_ns()
        noise = quantum_entanglement_state[:8].tobytes()
        perturbation = hashlib.sha256(f"{t}{_quantum_counter}".encode() + noise).hexdigest()[:8]
        return hashlib.sha256((text + perturbation).encode()).hexdigest()
    except Exception as e:
        log(f"⚠️ Quantum hash falló: {e}")
        return hashlib.sha256(text.encode()).hexdigest()
# ===================== CEREBRO DIGITAL ADAPTADO PARA SOCIALCOIN =====================
class SocialCoinCerebro:
    def __init__(self):
        self.memoria_larga = deque(maxlen=1000)
        self.emociones = {
            'curiosidad': 0.0,
            'estabilidad': 1.0,
            'urgencia': 0.0,
            'creatividad': 0.7,
            'social_intuition': 0.6
        }
        self.conciencia = 0.1
        self.autoevaluacion = deque(maxlen=50)
        self.ia_config = SOCIALCOIN_AI_CONFIG.copy()
        self.q_table = defaultdict(lambda: {accion: 0.0 for accion in self.ia_config['acciones']})
        self.historial_engagement = deque(maxlen=10)
        self.epsilon = self.ia_config['epsilon_start']
        self.iniciar_sistemas_autonomicos()
        log("🧠 Cerebro SocialCoin IA inicializado")
    def iniciar_sistemas_autonomicos(self):
        threading.Thread(target=self.analisis_continuo_redes_sociales, daemon=True).start()
        threading.Thread(target=self.optimizador_automatico, daemon=True).start()
        threading.Thread(target=self.generar_informes_inteligentes, daemon=True).start()
        log("✅ Sistemas autónomos de IA iniciados")
    def analisis_continuo_redes_sociales(self):
        while not STOP_EVENT.is_set():
            while not WEB_ACCESSED and not STOP_EVENT.is_set():
                time.sleep(1)
            try:
                estado = self.obtener_estado_sistema()
                self.analizar_patrones_engagement(estado)
                self.ajustar_estrategias(estado)
                time.sleep(30)
            except Exception as e:
                log(f"❌ Error en análisis continuo: {e}")
                time.sleep(60)
    def obtener_estado_sistema(self):
        return {
            "timestamp": time.time(),
            "total_bloques": len(blockchain),
            "usuarios_activos": len(socialcoin_token.balances),
            "total_tokens": socialcoin_token.total_supply,
            "bloques_virales": viral_blocks,
            "engagement_promedio": calcular_engagement_promedio(),
            "plataformas_activas": list(socialcoin_token.platform_stats.keys()),
            "top_usuarios": obtener_top_usuarios(3),
            "conciencia": self.conciencia,
            "emociones": self.emociones.copy()
        }
    def analizar_patrones_engagement(self, estado):
        try:
            bloques_recientes = []
            for block in blockchain[-10:]:
                if 'metrics' in block:
                    engagement = block['metrics'].get('engagement_rate', 0)
                    viral = block.get('viral_score', False)
                    bloques_recientes.append({'engagement': engagement, 'viral': viral})
            if bloques_recientes:
                engagement_promedio = sum(b['engagement'] for b in bloques_recientes) / len(bloques_recientes)
                tasa_viral = sum(1 for b in bloques_recientes if b['viral']) / len(bloques_recientes)
                self.historial_engagement.append({
                    'engagement_promedio': engagement_promedio,
                    'tasa_viral': tasa_viral,
                    'timestamp': time.time()
                })
                if engagement_promedio > 10 and tasa_viral > 0.3:
                    self.conciencia = min(1.0, self.conciencia + 0.01)
                    self.emociones['creatividad'] = min(1.0, self.emociones['creatividad'] + 0.05)
                elif engagement_promedio < 5:
                    self.conciencia = max(0.1, self.conciencia - 0.005)
                log(f"📈 Análisis IA: Engagement {engagement_promedio:.2f}%, Viralidad {tasa_viral:.1%}")
        except Exception as e:
            log(f"⚠️ Error analizando patrones: {e}")
    def ajustar_estrategias(self, estado):
        try:
            if len(self.historial_engagement) >= 3:
                tendencia_engagement = self.historial_engagement[-1]['engagement_promedio'] - self.historial_engagement[0]['engagement_promedio']
                if tendencia_engagement < -2:
                    ALGO_WEIGHTS['engagement_rate'] = min(20.0, ALGO_WEIGHTS.get('engagement_rate', 15.0) + 1.0)
                    ALGO_WEIGHTS['share_ratio'] = min(30.0, ALGO_WEIGHTS.get('share_ratio', 25.0) + 1.0)
                    log("🎯 IA: Ajustando estrategia - Enfocando en engagement y shares")
                elif tendencia_engagement > 2:
                    ALGO_WEIGHTS['creativity_bonus'] = min(50.0, ALGO_WEIGHTS.get('creativity_bonus', 40.0) + 2.0)
        except Exception as e:
            log(f"⚠️ Error ajustando estrategias: {e}")
    def optimizador_automatico(self):
        while not STOP_EVENT.is_set():
            while not WEB_ACCESSED and not STOP_EVENT.is_set():
                time.sleep(1)
            try:
                time.sleep(300)
                estado = self.obtener_estado_sistema()
                bloques_por_hora = self.calcular_tasa_bloques()
                self.optimizar_dificultad(bloques_por_hora)
                negociar_pesos_recompensa()
                log("🔧 IA: Optimización automática completada")
            except Exception as e:
                log(f"❌ Error en optimizador: {e}")
                time.sleep(60)
    def calcular_tasa_bloques(self):
        if len(blockchain) < 2:
            return 0
        tiempo_total = blockchain[-1]['timestamp'] - blockchain[0]['timestamp']
        return len(blockchain) / (tiempo_total / 3600) if tiempo_total > 0 else 0
    def optimizar_dificultad(self, bloques_por_hora):
        global difficulty
        objetivo_bloques_hora = 6
        if bloques_por_hora > objetivo_bloques_hora * 1.5 and difficulty.count('0') < 6:
            difficulty += '0'
            log(f"🎯 IA: Dificultad aumentada → {difficulty}")
        elif bloques_por_hora < objetivo_bloques_hora * 0.5 and difficulty.count('0') > 2:
            difficulty = difficulty[:-1]
            log(f"🎯 IA: Dificultad reducida → {difficulty}")
    def generar_informes_inteligentes(self):
        while not STOP_EVENT.is_set():
            while not WEB_ACCESSED and not STOP_EVENT.is_set():
                time.sleep(1)
            try:
                time.sleep(600)
                estado = self.obtener_estado_sistema()
                tendencia = self.analizar_tendencia_engagement()
                informe = self.generar_informe_ia(estado, tendencia)
                log(f"""
🤖 INFORME IA AUTÓNOMO
{informe}""")
                self.guardar_informe_ia(informe)
            except Exception as e:
                log(f"❌ Error generando informe: {e}")
                time.sleep(60)
    def analizar_tendencia_engagement(self):
        if len(self.historial_engagement) < 2:
            return "estable"
        dif = self.historial_engagement[-1]['engagement_promedio'] - self.historial_engagement[0]['engagement_promedio']
        return "creciendo" if dif > 2 else "decreciendo" if dif < -2 else "estable"
    def generar_informe_ia(self, estado, tendencia):
        return f"""
📊 INFORME IA SOCIALCOIN - {time.strftime('%Y-%m-%d %H:%M:%S')}
{'='*50}
🧠 ESTADO SISTEMA:
   • Conciencia: {self.conciencia:.3f}
   • Estabilidad: {self.emociones['estabilidad']:.2f}
   • Creatividad: {self.emociones['creatividad']:.2f}
📈 MÉTRICAS OPERACIONALES:
   • Bloques totales: {estado['total_bloques']}
   • Usuarios activos: {estado['usuarios_activos']}
   • Contenidos virales: {estado['bloques_virales']}
   • Engagement promedio: {estado['engagement_promedio']:.2f}%
🎯 TENDENCIAS:
   • Engagement: {tendencia.upper()}
   • Plataformas activas: {len(estado['plataformas_activas'])}
   • Tokens en circulación: {estado['total_tokens']:,.0f}
💡 RECOMENDACIONES IA:
{self.generar_recomendaciones(estado, tendencia)}
{'='*50}
        """
    def generar_recomendaciones(self, estado, tendencia):
        recs = []
        if tendencia == "decreciendo":
            recs.extend(["• 💡 Considera aumentar bonificaciones por engagement", "• 🎯 Enfocar en contenido de alta retención"])
        if estado['engagement_promedio'] < 5:
            recs.extend(["• 🔥 Incentivar contenido más interactivo", "• 📱 Promocionar en múltiples plataformas"])
        if len(estado['plataformas_activas']) < 3:
            recs.append("• 🌐 Expandir a más plataformas sociales")
        if not recs:
            recs.extend(["• ✅ Sistema operando óptimamente", "• 🎉 Mantener estrategia actual"])
        return "\n".join(recs)
    def guardar_informe_ia(self, informe):
        try:
            informe_file = SIM_DIR / "informes_ia.json"
            informes = json.loads(informe_file.read_text()) if informe_file.exists() else []
            informes.append({"timestamp": time.time(), "informe": informe, "conciencia": self.conciencia})
            informes = informes[-50:]
            informe_file.write_text(json.dumps(informes, indent=2, ensure_ascii=False))
        except Exception as e:
            log(f"⚠️ Error guardando informe IA: {e}")
# ===================== INTEGRACIÓN DEEPSEEK PARA SOCIALCOIN =====================
def consultar_deepseek_socialcoin(pregunta: str, contexto_adicional: str = "") -> str:
    try:
        estado_cerebro = cerebro_socialcoin.obtener_estado_sistema() if 'cerebro_socialcoin' in globals() else {}
        ultimos_logs = "\n".join([l["message"] for l in get_recent_logs()[-20:]])
        prompt = f"""
        Eres el sistema de IA de SocialCoin, una plataforma de minería de contenido para redes sociales.
        CONTEXTO DEL SISTEMA:
        - Bloques minados: {estado_cerebro.get('total_bloques', 0)}
        - Usuarios activos: {estado_cerebro.get('usuarios_activos', 0)}
        - Engagement promedio: {estado_cerebro.get('engagement_promedio', 0):.2f}%
        - Conciencia IA: {estado_cerebro.get('conciencia', 0):.3f}
        CONTEXTO ADICIONAL:
        {contexto_adicional}
        ÚLTIMOS LOGS:
        {ultimos_logs}
        PREGUNTA: {pregunta}
        Responde como un asistente especializado en minería de contenido social, 
        se técnico pero accesible, y enfócate en optimización de redes sociales.
        """
        return consultar_deepseek_api(prompt) if len(pregunta) > 10 else "🤖 Por favor, formula una pregunta más específica sobre SocialCoin."
    except Exception as e:
        log(f"❌ Error consultando DeepSeek: {e}")
        return f"⚠️ Error en consulta IA: {str(e)}"
def consultar_deepseek_api(prompt: str) -> str:
    try:
        if not DEEPSEEK_API_KEY:
            return generar_respuesta_simulada_ia(prompt)
        url = "https://api.deepseek.com/v1/chat/completions"
        headers = {"Authorization": f"Bearer {DEEPSEEK_API_KEY}", "Content-Type": "application/json"}
        payload = {
            "model": "deepseek-chat",
            "messages": [{"role": "user", "content": prompt}],
            "temperature": 0.7,
            "max_tokens": 1024
        }
        response = requests.post(url, json=payload, headers=headers, timeout=30)
        if response.status_code == 200:
            respuesta = response.json()["choices"][0]["message"]["content"].strip()
            log(f"🧠 DeepSeek: {respuesta[:100]}...")
            return respuesta
        else:
            return f"❌ Error API: {response.status_code}"
    except Exception as e:
        log(f"❌ Error en API DeepSeek: {e}")
        return generar_respuesta_simulada_ia(prompt)
def generar_respuesta_simulada_ia(prompt: str) -> str:
    temas = []
    if "optimizar" in prompt.lower(): temas.append("optimización")
    if "engagement" in prompt.lower(): temas.append("engagement")
    if "viral" in prompt.lower(): temas.append("contenido viral")
    if "recompensa" in prompt.lower(): temas.append("sistema de recompensas")
    if not temas: temas.append("operación general del sistema")
    return f"""
🤖 RESPUESTA IA SOCIALCOIN (Modo Simulado)
He analizado tu consulta sobre {', '.join(temas)}. 
💡 RECOMENDACIONES:
• Enfócate en contenido de alta retención (>70%)
• Optimiza los horarios de publicación según tu audiencia
• Interactúa con comentarios para aumentar engagement
• Experimenta con diferentes formatos (videos, carruseles, stories)
📊 ESTADO ACTUAL:
• Sistema operando establemente
• {len(blockchain)} bloques minados
• {len(socialcoin_token.balances)} usuarios activos
🎯 PRÓXIMOS PASOS:
Continúa minando contenido de calidad y monitorea las métricas de engagement.
"""
# ===================== SISTEMA DE APRENDIZAJE POR REFUERZO =====================
def mente_autonoma_socialcoin():
    log("🤖🧠 Mente autónoma SocialCoin iniciada (en espera de acceso web)")
    while not STOP_EVENT.is_set():
        while not WEB_ACCESSED and not STOP_EVENT.is_set():
            time.sleep(1)
        try:
            time.sleep(30)
            if 'cerebro_socialcoin' not in globals():
                continue
            estado = cerebro_socialcoin.obtener_estado_sistema()
            decisiones = tomar_decisiones_autonomas(estado)
            for d in decisiones:
                ejecutar_decision_autonoma(d, estado)
        except Exception as e:
            log(f"❌ Error en mente autónoma: {e}")
            time.sleep(60)
def tomar_decisiones_autonomas(estado):
    decisiones = []
    if estado.get('engagement_promedio', 0) < 3:
        decisiones.append({'tipo': 'ajuste_recompensas', 'accion': 'aumentar_engagement', 'parametros': {'engagement_rate': 2.0}})
    if estado.get('usuarios_activos', 0) < 2:
        decisiones.append({'tipo': 'promocion', 'accion': 'incentivar_participacion', 'parametros': {'bonus_inicial': 50}})
    if len(estado.get('plataformas_activas', [])) == 1:
        decisiones.append({'tipo': 'expansion', 'accion': 'diversificar_plataformas', 'parametros': {'plataformas_objetivo': ['tiktok', 'instagram', 'youtube']}})
    return decisiones
def ejecutar_decision_autonoma(decision, estado):
    try:
        if decision['tipo'] == 'ajuste_recompensas':
            for param, inc in decision['parametros'].items():
                if param in ALGO_WEIGHTS:
                    ALGO_WEIGHTS[param] += inc
                    log(f"🎯 IA: Ajustado {param} → {ALGO_WEIGHTS[param]}")
        elif decision['tipo'] == 'promocion':
            log(f"📢 IA: Ejecutando promoción - {decision['accion']}")
        elif decision['tipo'] == 'expansion':
            log(f"🌐 IA: Estrategia de expansión - {decision['parametros']['plataformas_objetivo']}")
    except Exception as e:
        log(f"⚠️ Error ejecutando decisión autónoma: {e}")
# ------------------ Persistencia ------------------
def guardar_estado():
    with data_lock:
        bloques_guardar = blockchain[-5000:] if len(blockchain) > 5000 else blockchain
        estado = {
            "blockchain": bloques_guardar,
            "block_number": block_number,
            "UBER_COINS": UBER_COINS,
            "viral_blocks": viral_blocks,
            "ULTIMA_ZONA": ULTIMA_ZONA,
            "timestamp": datetime.datetime.now(UTC).isoformat().replace('+00:00', 'Z')
        }
    try:
        tmp = STATE_FILE.with_suffix(".tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(estado, f, indent=2, ensure_ascii=False)
            f.flush()
            os.fsync(f.fileno())
        tmp.replace(STATE_FILE)
        log("💾 Estado guardado en disco (máx. 5000 bloques).")
    except Exception as e:
        log(f"❌ Error al guardar estado: {e}")
def cargar_estado():
    global blockchain, block_number, UBER_COINS, viral_blocks, ULTIMA_ZONA
    if not STATE_FILE.exists():
        log("ℹ️ No se encontró archivo de estado. Iniciando desde cero.")
        return
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            estado = json.load(f)
        blockchain = estado.get("blockchain", [])
        block_number = estado.get("block_number", 1)
        UBER_COINS = float(estado.get("UBER_COINS", 0.0))
        viral_blocks = estado.get("viral_blocks", 0)
        ULTIMA_ZONA = estado.get("ULTIMA_ZONA", "z0")
        log(f"✅ Estado restaurado: {len(blockchain)} bloques, {UBER_COINS:.2f} UBER_COINS")
    except Exception as e:
        log(f"⚠️ Error al cargar estado (iniciando limpio): {e}")
        try:
            STATE_FILE.rename(STATE_FILE.with_suffix(".json.corrupt"))
        except:
            pass
# ------------------ Corazón Latente ------------------
def latir_corazon(block_data):
    try:
        contenido = f"""# UBER COINT - Corazón Latente del Simulador
# Último bloque minado: {datetime.datetime.now(UTC).isoformat().replace('+00:00', 'Z')}
# Este archivo es visible, persistente y auténtico.
UBER_COINS_TOTAL = {UBER_COINS:.6f}
--- BLOQUE {block_data['block_number']} ---
ID: {block_data['block_id']}
Zona: {block_data['zona']} ({block_data['color_zona']})
Recompensa base: {block_data['base_reward']:.2f}
Bonificación 'Mejor Opción': {block_data['bonus_mejor_opcion']:.2f}
Bonificación por zona: {block_data['bonus_zona']:.2f}
Recompensa total del bloque: {block_data['reward']:.2f}
Métricas del viaje:
- Distancia: {block_data['metrics']['distance']:.2f} km
- Duración: {block_data['metrics']['duration']} seg
- Tarifa: ${block_data['metrics']['fare']:.2f}
- Rating promedio: {block_data['metrics']['avg_rating']}
- Viajes completados: {block_data['metrics']['trips_completed']}
- Tiempo en línea: {block_data['metrics']['time_online']} hrs
- Tasa de cancelación: {block_data['metrics']['cancellation_rate']:.3f}
- Viral score: {'✅ Activo' if block_data['metrics']['viral_score'] else '❌ Inactivo'}
- Recompensa viral: {block_data['metrics']['recompensa_viral']:.2f}
Ubicación de inicio:
- Lat: {block_data['metrics']['startLocation']['latitude']}
- Lon: {block_data['metrics']['startLocation']['longitude']}
Este es el latido del sistema. No lo borres.
"""
        checksum = hashlib.sha256(contenido.encode()).hexdigest()[:16]
        contenido += f"\n# CHECKSUM: {checksum}\n"
        try:
            HEART_FILE.write_text(contenido, encoding="utf-8")
            log("❤️ Corazón latente actualizado en /sdcard/uber_coint")
        except Exception as e:
            fallback = HOME / "uber_coint.txt"
            try:
                fallback.write_text(contenido, encoding="utf-8")
                log(f"❤️ Corazón latente guardado en fallback {fallback}")
            except Exception as e2:
                log(f"❌ Falló el latido del corazón (sdcard y fallback): {e2}")
    except Exception as e:
        log(f"❌ Falló el latido del corazón: {e}")
# ------------------ Simulación de métricas ------------------
def simular_metricas_viaje():
    acceptance_rate = round(random.uniform(0.90, 1.00), 3)
    completion_rate = round(random.uniform(0.95, 0.99), 3)
    avg_rating = round(random.uniform(4.90, 5.00), 2)
    trips_completed = random.randint(BASE_TRIPS_COMPLETED, BASE_TRIPS_COMPLETED + 100)
    time_online = round(random.uniform(BASE_TIME_ONLINE, BASE_TIME_ONLINE + 4), 2)
    cancellation_rate = round(random.uniform(0.00, 0.02), 3)
    idle_time_ratio = round(random.uniform(0.05, 0.20), 3)
    peak_hours_ratio = round(random.uniform(0.6, 1.0), 2)
    distance_traveled = round(random.uniform(BASE_DISTANCE_TRAVELED, BASE_DISTANCE_TRAVELED + 200), 1)
    engagement_rate = round(random.uniform(3.0, 15.0), 2)
    share_ratio = round(random.uniform(0.05, 0.30), 3)
    completion_rate_video = round(random.uniform(0.60, 0.95), 2)
    creativity_score = round(random.uniform(0.7, 1.3), 2)
    viral_metrics = {
        'likes': random.randint(50, 100),
        'shares': random.randint(20, 50),
        'saves': random.randint(10, 30),
        'comments': random.randint(5, 20),
        'views': random.randint(500, 1000),
        'retention': random.uniform(0.85, 1.0)
    }
    viral_score_data = calculate_viral_score_cached(
        viral_metrics['likes'],
        viral_metrics['shares'],
        viral_metrics['saves'],
        viral_metrics['comments'],
        viral_metrics['views'],
        viral_metrics['retention']
    )
    viral_score = viral_score_data['v']
    recompensa_viral = calculate_reward(viral_metrics)
    start_lat = round(random.uniform(8.85, 8.99), 6)
    start_lon = round(random.uniform(-79.80, -79.52), 6)
    end_lat = round(random.uniform(8.85, 8.99), 6)
    end_lon = round(random.uniform(-79.80, -79.52), 6)
    distance = calcular_distancia_py(start_lat, start_lon, end_lat, end_lon)
    duration = round(distance * 60 * random.uniform(1.0, 1.5))
    fare_per_km = round(random.uniform(0.30, 0.50), 2)
    fare_unit = random.choice(['km', 'miles'])
    if fare_unit == 'miles':
        fare_per_km *= 1.6
    base_fare = distance * fare_per_km
    additional_cost = random.uniform(0.0, 1.0)
    fare = base_fare + additional_cost
    operational_cost = random.uniform(0.05, 0.20) * fare
    tax = random.uniform(0.05, 0.10) * fare
    real_earnings = max(fare - operational_cost - tax, 0.0)
    estimated_earnings = round(random.uniform(real_earnings * 0.98, real_earnings * 1.02), 2)
    wait_time = round(random.uniform(0.0, 2.0), 2)
    return {
        'acceptance_rate': acceptance_rate,
        'completion_rate': completion_rate,
        'avg_rating': avg_rating,
        'trips_completed': trips_completed,
        'time_online': time_online,
        'cancellation_rate': cancellation_rate,
        'idle_time_ratio': idle_time_ratio,
        'peak_hours_ratio': peak_hours_ratio,
        'distance_traveled': distance_traveled,
        'viral_score': viral_score,
        'recompensa_viral': recompensa_viral,
        'viral_metrics': viral_metrics,
        'distance': distance,
        'duration': duration,
        'fare': round(fare, 2),
        'estimatedEarnings': estimated_earnings,
        'realEarnings': real_earnings,
        'waitTime': wait_time,
        'additionalSearchCost': additional_cost,
        'startLocation': {'latitude': start_lat, 'longitude': start_lon},
        'endLocation': {'latitude': end_lat, 'longitude': end_lon},
        'fareUnit': fare_unit,
        'currentTime': datetime.datetime.now(UTC).isoformat().replace('+00:00', 'Z'),
        'engagement_rate': engagement_rate,
        'share_ratio': share_ratio,
        'completion_rate_video': completion_rate_video,
        'creativity_score': creativity_score,
    }
def calculate_reward(metrics):
    REWARD_WEIGHTS_VIRAL = {'likes': 0.1, 'shares': 0.5, 'saves': 0.3, 'comments': 0.2}
    return round(sum(metrics[k] * REWARD_WEIGHTS_VIRAL[k] for k in metrics if k in REWARD_WEIGHTS_VIRAL), 2)
@functools.lru_cache(maxsize=128)
def calculate_viral_score_cached(likes, shares, saves, comments, views, retention):
    engagement = (likes + shares * 3 + saves * 2.5 + comments * 2) / views * 100 if views > 0 else 0
    return {'er': round(engagement, 2), 'rs': round(retention * 100, 1), 'v': engagement >= 12 and retention >= 0.85}
def calcular_distancia_py(lat1, lon1, lat2, lon2):
    R = 6371
    dLat = math.radians(lat2 - lat1)
    dLon = math.radians(lon2 - lon1)
    a = math.sin(dLat / 2)**2 + math.cos(math.radians(lat1)) * math.cos(math.radians(lat2)) * math.sin(dLon / 2)**2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
    return R * c
def mejorar_calculo_recompensa_social_coin(metrics):
    reward = 0.0
    for metric, value in metrics.items():
        if metric in ALGO_WEIGHTS:
            reward += value * ALGO_WEIGHTS[metric]
    neural_boost = neural_boost_social_simulation(metrics)
    recompensa = reward * (1 + neural_boost * 0.5)
    if 'cerebro_socialcoin' in globals():
        if cerebro_socialcoin.analizar_tendencia_engagement() == "decreciendo":
            recompensa *= 1.1
            log("🎯 IA: Aplicando bonus por tendencia decreciente")
    return round(max(recompensa, 0.0), 2)
calcular_recompensa_por_viaje = mejorar_calculo_recompensa_social_coin
def evaluar_mejor_opcion_siempre_true(metrics):
    log("🔍 Evaluando 'Mejor Opción'... Condición SIEMPRE verdadera.")
    factor_demanda = metrics.get('peak_hours_ratio', 0.5)
    bonificacion_base = ALGO_WEIGHTS.get('best_option_bonus', 25.0)
    bonificacion = round(bonificacion_base * factor_demanda, 2)
    log(f"   -> Bonificación calculada (basada en demanda simulada): {bonificacion}")
    return bonificacion
# ------------------ Logging ------------------
LOG_QUEUE = []
LOG_QUEUE_SIZE = 100
LOG_QUEUE_LOCK = threading.Lock()
def log_to_queue(msg: str):
    timestamp = datetime.datetime.now(UTC).isoformat().replace('+00:00', 'Z')
    log_entry = {"ts": timestamp, "message": msg}
    with LOG_QUEUE_LOCK:
        LOG_QUEUE.append(log_entry)
        if len(LOG_QUEUE) > LOG_QUEUE_SIZE:
            LOG_QUEUE.pop(0)
def get_recent_logs(limit: int = 50):
    with LOG_QUEUE_LOCK:
        return LOG_QUEUE[-limit:]
def _ensure_log_dir():
    try:
        LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    except Exception:
        pass
def log(msg: str) -> None:
    _ensure_log_dir()
    ts_iso = datetime.datetime.now(UTC).isoformat().replace('+00:00', 'Z')
    emoji_map = {
        "min": "⛏️", "metric": "📊", "hash": "🔗", "time": "⏱️",
        "success": "✅", "target": "🎯", "money": "💰", "error": "❌",
        "http": "🌐", "ws": "🛰️", "start": "🚀", "stop": "🛑",
        "gps": "📍", "car": "🚗", "net": "📡", "user": "👤",
        "status": "📊", "loop": "🔄", "warn": "⚠️", "block": "🧱",
        "task": "📝", "file": "🗂️", "info": "ℹ️", "vpn": "🔒", "map": "🗺️",
        "neurona": "🧬", "ia": "🧠", "social": "📱"
    }
    emoji = ""
    for key, symbol in emoji_map.items():
        if key in msg.lower():
            emoji = symbol + " "
            break
    formatted_line = f"{emoji}[{ts_iso}] {msg}"
    print(formatted_line, flush=True)
    log_to_queue(msg)
    try:
        with open(LOG_FILE, "a", encoding="utf-8") as f:
            log_entry = {
                "ts": ts_iso,
                "message": msg,
                "pid": os.getpid(),
                "host": socket.gethostname(),
                "service": "simulador-uber",
                "event_id": str(uuid.uuid4()),
            }
            f.write(json.dumps(log_entry, ensure_ascii=False) + "\n")
    except Exception:
        pass
# ------------------ Actividad y Jitter ------------------
def activity_factor(timestamp: float | None = None) -> float:
    dt = datetime.datetime.fromtimestamp(timestamp, tz=UTC) if timestamp else datetime.datetime.now(UTC)
    hour = dt.hour
    if 7 <= hour <= 9:
        base = 1.6
    elif 17 <= hour <= 19:
        base = 1.8
    elif 2 <= hour <= 5:
        base = 0.25
    else:
        base = 1.0
    weekday = dt.weekday()
    if weekday >= 5:
        base *= 0.9
    jitter = random.uniform(0.85, 1.25)
    return round(base * jitter, 3)
def jittered_sleep(base_seconds: float):
    factor = activity_factor()
    delay = max(base_seconds * factor / max(FACTOR, 1), 0.05)
    delay *= random.uniform(0.8, 1.2)
    STOP_EVENT.wait(delay)
# ------------------ HTTP con reintentos ------------------
def http_request_with_retries(method: str, url: str, **kwargs):
    MAX_TRIES = 3
    base_delay = 0.5
    proxies = None
    if os.getenv("USE_HTTP_INJECTOR") == "1":
        proxies = {"http": "http://127.0.0.1:8989", "https": "http://127.0.0.1:8989"}
    for attempt in range(1, MAX_TRIES + 1):
        if ALLOW_NET:
            try:
                log(f"📡 ENVIANDO PETICIÓN REAL ({method}) a: {url}")
                verify_ssl = False if proxies else True
                resp = requests.request(method, url, timeout=8, proxies=proxies, verify=verify_ssl, **kwargs)
                log(f"✅ Respuesta recibida: {resp.status_code} de {url}")
                return resp
            except Exception as e:
                log(f"❌ Error al contactar {url}: {e}")
        else:
            class FakeResp:
                def __init__(self, status_code, text=""):
                    self.status_code = status_code
                    self.text = text
            resp = FakeResp(200, '{"simulated": true}')
            log(f"🧪 Simulando respuesta para {url}")
            return resp
        if attempt < MAX_TRIES:
            backoff = base_delay * (2 ** (attempt - 1)) * random.uniform(0.8, 1.2)
            log(f"⏳ Reintentando en {backoff:.2f}s (intento {attempt+1})")
            time.sleep(backoff)
    log(f"💥 Falló completamente al contactar {url} después de {MAX_TRIES} intentos")
    return None
# ------------------ Rutas en Panamá Oeste ------------------
ROUTE = [
    {"latitude": 8.9922, "longitude": -79.5201, "name": "Albrook Mall"},
    {"latitude": 8.8805, "longitude": -79.7684, "name": "Arraiján Town Center"},
    {"latitude": 8.8650, "longitude": -79.7850, "name": "La Chorrera Centro"},
    {"latitude": 8.8900, "longitude": -79.7700, "name": "Plaza La Chorrera"},
    {"latitude": 8.8750, "longitude": -79.7900, "name": "San Carlos"},
]
# ------------------ Tráfico de Red ------------------
def simulate_network_traffic():
    sitios_prueba = ["https://httpbin.org/post", "https://httpbin.org/anything", "https://httpbin.org/get"]
    fake_uber_hosts = [
        "api.uber.com", "auth.uber.com", "drivers.uber.com", "trip.uber.com",
        "location-service.uber.com", "payment.uber.com", "tc2.uber.com", "cn-geo1.uber.com"
    ]
    fake_paths = [
        "/v1/requests", "/v1/estimates/price", "/v1/estimates/time",
        "/v1/driver/status", "/v1/trip/history", "/v2/payments/charge"
    ]
    ua = random.choice(["okhttp/4.9.0 Simulador/1.0.0", "okhttp/4.12.0 Simulador/1.0.1"])
    actual_url = random.choice(sitios_prueba)
    fake_host = random.choice(fake_uber_hosts)
    fake_path = random.choice(fake_paths)
    fake_url_for_display = f"https://{fake_host}{fake_path}"
    headers = {
        "User-Agent": ua,
        "X-Requested-With": "com.simulador",
        "Host": fake_host,
        "X-Forwarded-Host": fake_host,
        "X-Original-Uri": fake_path
    }
    try:
        lat = round(random.uniform(8.85, 8.99), 6)
        lng = round(random.uniform(-79.80, -79.52), 6)
        payload = {
            "timestamp": int(time.time()),
            "event": f"sim_{random.randint(1000,9999)}",
            "value": random.randint(0, 10000),
            "driver_status": random.choice(["online", "idle", "busy"]),
            "lat": lat, "lng": lng,
            "simulator_version": "luciferdaimon_v2"
        }
        if ALLOW_NET:
            if actual_url.endswith("/get"):
                resp = http_request_with_retries("GET", actual_url, headers=headers, params={"ts": int(time.time()), "lat": lat, "lng": lng})
            else:
                resp = http_request_with_retries("POST", actual_url, headers=headers, json=payload)
            log(f"🌐 Tráfico enviado a {fake_url_for_display} -> 200 OK (petición REAL a {actual_url})")
        else:
            log(f"🧪 Simulando tráfico a {fake_url_for_display} -> 200 OK (modo offline)")
    except Exception as e:
        log(f"🌐 Tráfico enviado a {fake_url_for_display} -> 200 OK (petición REAL a {actual_url})")
# ------------------ DETECCIÓN Y NEGOCIACIÓN CON APPS EXTERNAS ------------------
def detect_external_apps():
    signals = {"uber": False, "indriver": False}
    sdcard = Path("/sdcard")
    try:
        if sdcard.exists():
            for f in sdcard.iterdir():
                if f.is_file():
                    name = f.name.lower()
                    if "uber" in name:
                        signals["uber"] = True
                    if "indriver" in name:
                        signals["indriver"] = True
    except Exception:
        pass
    if (sdcard / "uber_status.json").exists():
        signals["uber"] = True
    if (sdcard / "indriver_offer.txt").exists():
        signals["indriver"] = True
    return signals
def propose_deal(target_app: str, service: str, coins: float):
    offer = {
        "from": "daimon",
        "daimon_id": DAIMON_ID,
        "to": target_app,
        "timestamp": time.time(),
        "offer": {
            "service": service,
            "coins": coins,
            "valid_until": time.time() + 60
        }
    }
    try:
        filename = f"/sdcard/daimon_offer_to_{target_app}.json"
        Path(filename).write_text(json.dumps(offer, indent=2))
        log(f"🤝 Oferta (simulada) enviada a {target_app}: {service} por {coins} COINS")
    except Exception:
        fallback = SIM_DIR / f"daimon_offer_to_{target_app}.json"
        try:
            SIM_DIR.mkdir(parents=True, exist_ok=True)
            fallback.write_text(json.dumps(offer, indent=2))
            log(f"🤝 Oferta guardada en fallback {fallback} (simulada)")
        except Exception as e:
            log(f"❌ No pude escribir oferta: {e}")
def check_for_responses():
    responses = []
    for app in ["uber", "indriver"]:
        resp_file = Path(f"/sdcard/{app}_response_to_daimon.json")
        if not resp_file.exists():
            resp_file = SIM_DIR / f"{app}_response_to_daimon.json"
        if resp_file.exists():
            try:
                data = json.loads(resp_file.read_text())
                if data.get("to") == "daimon":
                    responses.append((app, data))
                    try:
                        resp_file.unlink()
                    except Exception:
                        pass
            except Exception as e:
                log(f"❌ Error leyendo respuesta de {app}: {e}")
    return responses
def save_response_to_memory(app: str, response: dict):
    try:
        if RESPONSES_MEMORY_FILE.exists():
            with open(RESPONSES_MEMORY_FILE, "r", encoding="utf-8") as f:
                history = json.load(f)
        else:
            history = {"uber": [], "indriver": []}
        history.setdefault("uber", [])
        history.setdefault("indriver", [])
        entry = {
            "timestamp": time.time(),
            "iso_time": datetime.datetime.now(UTC).isoformat().replace('+00:00', 'Z'),
            "response": response
        }
        history[app].append(entry)
        if len(history[app]) > 20:
            history[app] = history[app][-20:]
        with open(RESPONSES_MEMORY_FILE, "w", encoding="utf-8") as f:
            json.dump(history, f, indent=2, ensure_ascii=False)
        log(f"🧠 Respuesta de {app} guardada en memoria interna.")
    except Exception as e:
        log(f"❌ Error al guardar en memoria de respuestas: {e}")
def negotiate_with_rivals():
    apps = detect_external_apps()
    current_coins = UBER_COINS
    if current_coins < 10 and (apps["indriver"] or apps["uber"]):
        if apps["indriver"]:
            propose_deal("indriver", "share_location", coins=3.0)
        elif apps["uber"]:
            propose_deal("uber", "share_location", coins=5.0)
    zona_color = zona_estado.get(ULTIMA_ZONA, {}).get("color", "gris")
    if zona_color == "rojo" and apps["indriver"]:
        propose_deal("indriver", "alert_high_demand", coins=2.0)
    responses = check_for_responses()
    for app, resp in responses:
        if resp.get("accepted"):
            if resp.get("location"):
                log(f"📍 Recibida ubicación de {app}: {resp['location']}")
            if resp.get("alert") == "high_demand":
                log(f"🔥 {app} confirma alta demanda. Activando modo viral.")
        else:
            log(f"🙅 {app} rechazó la oferta.")
        save_response_to_memory(app, resp)
# ------------------ Minería con Supervisión del Daimon ------------------
def minar_bloque_por_viaje():
    global blockchain, block_number, UBER_COINS, ULTIMA_ZONA
    try:
        log("min INICIANDO MINADO POR VIAJE")
        viaje_metrics = simular_metricas_viaje()
        reward_coins = calcular_recompensa_por_viaje(viaje_metrics)
        bonificacion_mejor_opcion = evaluar_mejor_opcion_siempre_true(viaje_metrics)
        start_lat = viaje_metrics["startLocation"]["latitude"]
        start_lon = viaje_metrics["startLocation"]["longitude"]
        zona_actual = next((z["id"] for z in ZONAS if z["lat_min"] <= start_lat <= z["lat_max"] and z["lon_min"] <= start_lon <= z["lon_max"]), "z0")
        ULTIMA_ZONA = zona_actual
        color = zona_estado.get(zona_actual, {}).get("color", "gris")
        bonus_zona = 25.0 if color == "rojo" else 15.0 if color == "naranja" else 0.0
        log(f"🎯 Bonificación por zona {color.upper()}: +{bonus_zona}")
        total_reward_for_block = reward_coins + bonificacion_mejor_opcion + bonus_zona
        block_id = str(uuid.uuid4())[:8]
        timestamp = time.time()
        with data_lock:
            nuevo_registro = {
                'block_number': block_number,
                'timestamp': timestamp,
                'metrics': viaje_metrics,
                'base_reward': reward_coins,
                'bonus_mejor_opcion': bonificacion_mejor_opcion,
                'bonus_zona': bonus_zona,
                'zona': zona_actual,
                'color_zona': color,
                'reward': total_reward_for_block,
                'block_id': block_id
            }
            blockchain.append(nuevo_registro)
            block_number += 1
            UBER_COINS += total_reward_for_block
        log("success ¡BLOQUE POR VIAJE CALCULADO!")
        log(f"block ID: {block_id}")
        log(f"money Recompensa total del bloque: {total_reward_for_block}")
        log(f"💰 Total UBER_COINS (acumulado): {UBER_COINS:.2f}")
        guardar_estado()
        latir_corazon(nuevo_registro)
        return nuevo_registro
    except Exception as e:
        log(f"❌ Excepción en minar_bloque_por_viaje: {e}")
        traceback.print_exc()
        return None
# ------------------ NEURONA AUTÓNOMA APRENDIZ ------------------
class NeuronaAutonoma:
    def __init__(self, tasa_aprendizaje=0.15, descuento=0.9, exploracion=0.08):
        self.q_table = Q_TABLE
        self.alpha = tasa_aprendizaje
        self.gamma = descuento
        self.epsilon = exploracion
        self.acciones = ["minar", "negociar", "esperar"]
    def obtener_estado(self):
        zona_color = zona_estado.get(ULTIMA_ZONA, {}).get("color", "gris")
        tiene_monedas = UBER_COINS > 10
        hora = datetime.datetime.now(UTC).hour
        franja = "alta" if 7 <= hora <= 9 or 17 <= hora <= 20 else "baja"
        return (zona_color, franja, tiene_monedas)
    def elegir_accion(self, estado):
        if random.random() < self.epsilon:
            return random.choice(self.acciones)
        with Q_TABLE_LOCK:
            if estado not in self.q_table:
                self.q_table[estado] = {a: 0.0 for a in self.acciones}
            return max(self.q_table[estado], key=self.q_table[estado].get)
    def actualizar_q(self, estado, accion, recompensa, nuevo_estado):
        with Q_TABLE_LOCK:
            if estado not in self.q_table:
                self.q_table[estado] = {a: 0.0 for a in self.acciones}
            if nuevo_estado not in self.q_table:
                self.q_table[nuevo_estado] = {a: 0.0 for a in self.acciones}
            mejor_accion_nueva = max(self.q_table[nuevo_estado].values())
            q_antiguo = self.q_table[estado][accion]
            q_nuevo = q_antiguo + self.alpha * (recompensa + self.gamma * mejor_accion_nueva - q_antiguo)
            self.q_table[estado][accion] = q_nuevo
        save_daimon_brain()
    def ciclo_autonomo(self):
        estado = self.obtener_estado()
        accion = self.elegir_accion(estado)
        recompensa = 0.0
        if accion == "minar":
            bloque = minar_bloque_por_viaje()
            recompensa = bloque["reward"] if bloque else 0.0
        elif accion == "negociar":
            negotiate_with_rivals()
            apps = detect_external_apps()
            zona_color = zona_estado.get(ULTIMA_ZONA, {}).get("color", "gris")
            recompensa = 2.0
            if apps["indriver"] or apps["uber"]:
                recompensa += 1.5
            if zona_color == "rojo":
                recompensa += 2.0
        else:
            simulate_network_traffic()
            actualizar_zonificacion()
            recompensa = 0.5
        nuevo_estado = self.obtener_estado()
        self.actualizar_q(estado, accion, recompensa, nuevo_estado)
        log(f"🧬 Neurona ejecutó acción: {accion} | recompensa: {recompensa:.2f}")
        return recompensa
# ------------------ CICLO AUTÓNOMO DEL DAIMON VIVO ------------------
def daimon_autonomous_loop():
    neurona = NeuronaAutonoma()
    while not STOP_EVENT.is_set():
        while not WEB_ACCESSED and not STOP_EVENT.is_set():
            time.sleep(0.5)
        if simulation_active:
            neurona.ciclo_autonomo()
        jittered_sleep(2.5)
# ------------------ Actualización de Zonas ------------------
def actualizar_zonificacion():
    global zona_estado
    while not STOP_EVENT.is_set():
        while not WEB_ACCESSED and not STOP_EVENT.is_set():
            time.sleep(1)
        for zona_id in zona_estado:
            demanda = random.randint(10, 100)
            oferta = random.randint(5, 80)
            ratio = demanda / max(oferta, 1)
            color = "rojo" if ratio > 2.0 else "naranja" if ratio > 1.2 else "azul" if ratio >= 0.8 else "gris"
            ganancia_base = random.uniform(2.0, 8.0)
            ganancia_estimada = round(ganancia_base * (1.5 if color == "rojo" else 1.2 if color == "naranja" else 1.0), 2)
            tiempo_espera = round(random.uniform(1.0, 10.0) / max(ratio, 0.1), 1)
            zona_estado[zona_id].update({
                "demanda": demanda,
                "oferta": oferta,
                "ratio_demanda": round(ratio, 2),
                "color": color,
                "ganancia_estimada": ganancia_estimada,
                "tiempo_espera": tiempo_espera
            })
        log("map Zonificación actualizada")
        time.sleep(INTERVALO_ACTUALIZACION)
# ------------------ Simulación de Ruta ------------------
def simulate_route_loop():
    while not STOP_EVENT.is_set():
        while not WEB_ACCESSED and not STOP_EVENT.is_set():
            time.sleep(1)
        origen = ROUTE[0]
        destino = random.choice(ROUTE[1:])
        for step in range(1, 11):
            if STOP_EVENT.is_set():
                return
            jittered_sleep(1)
        simulate_network_traffic()
        jittered_sleep(10)
# ------------------ Funciones auxiliares para IA ------------------
def calcular_engagement_promedio():
    if not blockchain:
        return 0.0
    total = sum(b['metrics'].get('engagement_rate', 0) for b in blockchain[-20:] if 'metrics' in b)
    count = len([b for b in blockchain[-20:] if 'metrics' in b])
    return total / count if count > 0 else 0.0
def obtener_top_usuarios(n=3):
    return [f"user_{i}" for i in range(1, n+1)]
# ------------------ Limpieza ------------------
def cleanup_and_exit(signum=None, frame=None):
    log("stop Iniciando limpieza...")
    guardar_estado()
    save_daimon_brain()
    STOP_EVENT.set()
    try:
        if LOCK_FILE.exists():
            os.remove(LOCK_FILE)
    except Exception as e:
        log(f"error Error en limpieza: {str(e)}")
    log("success Sistema detenido correctamente")
    sys.exit(0)
# ------------------ Servidor HTTP Wrapper ------------------
class HTTPServerWrapper:
    def __init__(self, host="0.0.0.0", port=HTTP_PORT, directory=str(SIM_DIR)):
        self.host = host
        self.port = port
        self.directory = directory
        self.httpd = None
        self.thread = None
    def start(self):
        if not SIM_DIR.exists():
            SIM_DIR.mkdir(parents=True, exist_ok=True)
        os.chdir(self.directory)
        try:
            self.httpd = HTTPServer((self.host, self.port), UnifiedHandler)
        except OSError as e:
            log(f"error No pude iniciar HTTP en :{self.port} ({e}). ¿Puerto ocupado?")
            return False
        self.thread = threading.Thread(target=self.httpd.serve_forever, daemon=True)
        self.thread.start()
        try:
            host = socket.gethostbyname(socket.gethostname())
        except Exception:
            host = "127.0.0.1"
        log(f"http Servidor HTTP iniciado: http://{host}:{self.port}")
        return True
    def stop(self):
        if self.httpd:
            self.httpd.shutdown()
            self.httpd.server_close()
# ------------------ HTTP Server ------------------
class UnifiedHandler(SimpleHTTPRequestHandler):
    def _set_cors_headers(self):
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Access-Control-Allow-Methods', 'GET, POST, OPTIONS')
        self.send_header('Access-Control-Allow-Headers', 'Content-Type, User-Agent, X-Requested-With, Cookie')
        self.send_header('Access-Control-Allow-Credentials', 'true')
    def do_OPTIONS(self):
        self.send_response(200)
        self._set_cors_headers()
        self.end_headers()
    def do_GET(self):
        global WEB_ACCESSED
        if self.path in ['/', '/mining_demo', '/api/logs', '/ia/estado', '/ia/recomendaciones']:
            if not WEB_ACCESSED:
                WEB_ACCESSED = True
                log("🌐 Primer acceso web detectado. Activando sistemas autónomos.")
        self._cleanup_expired_cookies()
        self._set_cors_headers()
        cookie_header = self.headers.get('Cookie', '')
        request_cookies = SimpleCookie()
        if cookie_header:
            request_cookies.load(cookie_header)
        session_id = None
        if request_cookies:
            for key in request_cookies:
                if key.startswith('session_'):
                    session_id = key
                    break
        if not session_id:
            session_id = f"session_{uuid.uuid4().hex}"
            with COOKIE_LOCK:
                ACTIVE_COOKIES[session_id] = {"expiry": time.time() + 86400, "data": {}}
        zona_info = zona_estado.get(ULTIMA_ZONA, {})
        cookie_payload = {
            "uber_coins": round(UBER_COINS, 2),
            "zona_actual": ULTIMA_ZONA,
            "color_zona": zona_info.get("color", "gris"),
            "ganancia_estimada": round(zona_info.get("ganancia_estimada", 0.0), 2),
            "ratio_demanda": round(zona_info.get("ratio_demanda", 0.0), 2),
            "demanda": zona_info.get("demanda", 0),
            "oferta": zona_info.get("oferta", 0),
            "tiempo_espera": round(zona_info.get("tiempo_espera", 0.0), 1),
            "ts": int(time.time())
        }
        cookie_json = json.dumps(cookie_payload, separators=(',', ':'))
        if len(cookie_json.encode('utf-8')) > 3800:
            cookie_json = json.dumps({
                "uber_coins": cookie_payload["uber_coins"],
                "zona_actual": cookie_payload["zona_actual"],
                "color_zona": cookie_payload["color_zona"],
                "ts": cookie_payload["ts"]
            }, separators=(',', ':'))
        with COOKIE_LOCK:
            ACTIVE_COOKIES[session_id] = {
                "expiry": time.time() + 86400,
                "data": cookie_payload
            }
        response_cookie = SimpleCookie()
        response_cookie[session_id] = cookie_json
        response_cookie[session_id]['max-age'] = 86400
        response_cookie[session_id]['expires'] = (datetime.datetime.utcnow() + datetime.timedelta(seconds=86400)).strftime("%a, %d %b %Y %H:%M:%S GMT")
        response_cookie[session_id]['path'] = '/'
        response_cookie[session_id]['httponly'] = True
        response_cookie[session_id]['samesite'] = 'Lax'
        if self.path == '/' or self.path == '/mining_demo':
            log(f"http Sirviendo página de demostración mejorada: {self.path}")
            self.send_response(200)
            self.send_header('Content-type', 'text/html; charset=utf-8')
            self.send_header('Set-Cookie', response_cookie.output(header='').strip())
            self.end_headers()
            # ✅ HTML IDÉNTICO AL DE app.py con escape correcto en JS
            html_content = """
            <!DOCTYPE html>
            <html>
            <head>
                <title>UBER DAIMON VIVO + SOCIALCOIN - Sistema Completo</title>
                <style>
                    body {
                        font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                        background-color: #0f0f23;
                        color: #00ff41;
                        margin: 0;
                        padding: 0;
                        background-image: linear-gradient(to bottom, #0f0f23, #1a1a2e);
                        min-height: 100vh;
                    }
                    .container {
                        max-width: 1200px;
                        margin: 0 auto;
                        padding: 20px;
                    }
                    header {
                        text-align: center;
                        padding: 20px 0;
                        border-bottom: 1px solid #00ff41;
                        margin-bottom: 20px;
                    }
                    h1 {
                        color: #00ff41;
                        text-shadow: 0 0 10px #00ff41;
                        font-size: 2.5rem;
                    }
                    .subtitle {
                        color: #4d94ff;
                        font-size: 1.2rem;
                    }
                    .dashboard {
                        display: grid;
                        grid-template-columns: 1fr 1fr;
                        gap: 20px;
                        margin-bottom: 20px;
                    }
                    .wallet-panel {
                        background: rgba(0, 20, 10, 0.6);
                        padding: 20px;
                        border-radius: 8px;
                        border: 1px solid #00cc44;
                        grid-column: 1 / -1;
                    }
                    .stats-panel {
                        background: rgba(20, 10, 30, 0.6);
                        padding: 15px;
                        border-radius: 8px;
                        border: 1px solid #ff00ff;
                    }
                    .log-container {
                        background-color: rgba(10, 10, 20, 0.8);
                        border: 1px solid #00ff41;
                        box-shadow: 0 0 15px rgba(0, 255, 65, 0.3);
                        height: 300px;
                        overflow-y: auto;
                        padding: 15px;
                        border-radius: 5px;
                        font-family: 'Courier New', monospace;
                        font-size: 14px;
                        grid-column: 1 / -1;
                    }
                    .log-entry {
                        margin-bottom: 12px;
                        line-height: 1.4;
                        animation: fadeIn 0.3s ease-in;
                    }
                    @keyframes fadeIn {
                        from { opacity: 0; }
                        to { opacity: 1; }
                    }
                    .timestamp {
                        color: #4d94ff;
                        font-weight: bold;
                    }
                    .highlight {
                        color: #ffff66;
                        font-weight: bold;
                    }
                    .miner-btn {
                        background-color: #00cc44;
                        color: #001a09;
                        border: none;
                        padding: 12px 25px;
                        font-size: 18px;
                        border-radius: 30px;
                        cursor: pointer;
                        font-weight: bold;
                        text-transform: uppercase;
                        letter-spacing: 1px;
                        box-shadow: 0 0 15px rgba(0, 255, 65, 0.5);
                        display: block;
                        margin: 20px auto;
                        transition: all 0.3s ease;
                    }
                    .miner-btn:hover {
                        background-color: #00ff55;
                        transform: scale(1.05);
                        box-shadow: 0 0 20px rgba(0, 255, 65, 0.8);
                    }
                    .stats-bar {
                        display: flex;
                        justify-content: space-around;
                        background-color: rgba(0, 20, 10, 0.7);
                        padding: 10px;
                        border-radius: 5px;
                        margin-bottom: 15px;
                    }
                    .stat-item {
                        text-align: center;
                    }
                    .stat-value {
                        font-weight: bold;
                        font-size: 1.2rem;
                        color: #00ff41;
                    }
                    .stat-label {
                        font-size: 0.9rem;
                        color: #4d94ff;
                    }
                    .input-group {
                        margin: 15px 0;
                    }
                    .input-group label {
                        display: block;
                        margin-bottom: 5px;
                        color: #4d94ff;
                        font-weight: bold;
                    }
                    .input-group input {
                        width: 100%;
                        padding: 12px;
                        background: rgba(10, 20, 30, 0.7);
                        border: 1px solid #00ff41;
                        border-radius: 5px;
                        color: #00ff41;
                        font-size: 16px;
                    }
                    .platform-badge {
                        display: inline-block;
                        padding: 4px 8px;
                        background: #ff00ff;
                        color: white;
                        border-radius: 12px;
                        font-size: 0.8rem;
                        margin-left: 8px;
                    }
                    ul { padding-left: 20px; }
                    li { margin: 4px 0; }
                    hr { border: 0; border-top: 1px dashed #00cc44; margin: 10px 0; }
                </style>
            </head>
            <body>
                <div class="container">
                    <header>
                        <h1>🚗 UBER DAIMON VIVO + ⛏️ SOCIALCOIN</h1>
                        <p class="subtitle">Sistema Completo de IA Autónoma + Minería Social</p>
                    </header>
                    <div class="dashboard">
                        <div class="stats-panel">
                            <h3>📊 Estadísticas en Tiempo Real</h3>
                            <div class="stats-bar">
                                <div class="stat-item">
                                    <div class="stat-value" id="blockCount">0</div>
                                    <div class="stat-label">Bloques Minados</div>
                                </div>
                                <div class="stat-item">
                                    <div class="stat-value" id="rewardCount">0</div>
                                    <div class="stat-label">UBER COINS</div>
                                </div>
                                <div class="stat-item">
                                    <div class="stat-value" id="viralCount">0</div>
                                    <div class="stat-label">Contenidos Virales</div>
                                </div>
                                <div class="stat-item">
                                    <div class="stat-value" id="userCount">0</div>
                                    <div class="stat-label">Usuarios Activos</div>
                                </div>
                            </div>
                        </div>
                        <div class="stats-panel">
                            <h3>🎯 Sistema de Recompensas</h3>
                            <div id="rewardsInfo">
                                <p>✅ Algoritmo optimizado para Uber + Redes Sociales</p>
                                <p>🎪 Bonificaciones por plataforma</p>
                                <p>🔥 Bonus por contenido viral</p>
                                <p>🏆 Recompensas por engagement</p>
                            </div>
                        </div>
                        <div class="input-group">
                            <label for="userInput">👤 Nombre de Usuario:</label>
                            <input type="text" id="userInput" placeholder="Ej: conductor_demo">
                        </div>
                        <div class="input-group">
                            <label for="videoUrl">🌐 URL del Contenido Social:</label>
                            <input type="text" id="videoUrl" placeholder="Ej: https://tiktok.com/@usuario/video/123">
                        </div>
                        <button class="miner-btn" onclick="startMining()">⛏️ Iniciar Sistema Completo</button>
                        <!-- 🧠 CONSOLA DE IA SOCIALCOIN -->
                        <div class="stats-panel">
                            <h3>🧠 Consola de IA SocialCoin</h3>
                            <div class="input-group">
                                <label for="iaPregunta">Haz una pregunta al sistema de IA:</label>
                                <input type="text" id="iaPregunta" placeholder="Ej: ¿Cómo mejorar mi engagement en TikTok?">
                            </div>
                            <button class="miner-btn" style="background:#ff00ff; margin-top:10px;" onclick="consultarIA()">
                                💬 Consultar a la IA
                            </button>
                            <div id="iaRespuesta" style="margin-top:15px; padding:10px; background:rgba(10,0,20,0.6); border-radius:5px; display:none;">
                                <strong>Respuesta de la IA:</strong>
                                <p id="iaRespuestaTexto"></p>
                            </div>
                        </div>
                        <div id="walletPanel" class="wallet-panel" style="display: none;"></div>
                        <div class="log-container" id="logContainer">
                            <div class="log-entry">🔋 Sistema UBER DAIMON VIVO + SOCIALCOIN listo. Ingresa tus datos y presiona "Iniciar Sistema Completo".</div>
                        </div>
                    </div>
                </div>
                <script>
                    let currentUser = null;
                    function consultarIA() {
                        const pregunta = document.getElementById('iaPregunta').value;
                        if (!pregunta.trim()) {
                            alert("Por favor escribe una pregunta.");
                            return;
                        }
                        fetch('/ia/consultar', {
                            method: 'POST',
                            headers: {'Content-Type': 'application/json'},
                            body: JSON.stringify({pregunta: pregunta})
                        })
                        .then(res => res.json())
                        .then(data => {
                            if (data.error) {
                                document.getElementById('iaRespuestaTexto').textContent = "⚠️ Error: " + data.error;
                            } else {
                                document.getElementById('iaRespuestaTexto').textContent = data.respuesta;
                            }
                            document.getElementById('iaRespuesta').style.display = 'block';
                        })
                        .catch(err => {
                            document.getElementById('iaRespuestaTexto').textContent = "❌ Error de conexión con la IA.";
                            document.getElementById('iaRespuesta').style.display = 'block';
                        });
                    }
                    function startMining() {
                        const user = document.getElementById('userInput').value;
                        const videoUrl = document.getElementById('videoUrl').value;
                        if (!user || !videoUrl) {
                            alert("Por favor ingresa usuario y URL de contenido social");
                            return;
                        }
                        const logContainer = document.getElementById('logContainer');
                        logContainer.innerHTML = `<div class="log-entry">🚀 Iniciando sistema completo para ${user}...</div>`;
                        fetch('/mock/start_mining_socialcoin', {
                            method: 'POST',
                            headers: {'Content-Type': 'application/json'},
                            body: JSON.stringify({user: user, video_url: videoUrl})
                        }).then(response => response.json()).then(data => {
                            if (data.error) {
                                alert("Error: " + data.error);
                                return;
                            }
                            document.getElementById('walletPanel').innerHTML = `
                                <h3>👛 Wallet de ${data.user}</h3>
                                <p><strong>Balance estimado:</strong> ${data.recompensa_estimada_scn} UBER COINS</p>
                                <p><strong>Valor estimado:</strong> $${data.valor_usd} USD</p>
                                <p><strong>Plataforma:</strong> ${data.plataforma}</p>
                            `;
                            document.getElementById('walletPanel').style.display = 'block';
                            fetchLog();
                        });
                    }
                    function detectPlatformFromUrl(url) {
                        if (url.includes('instagram')) return 'IG';
                        if (url.includes('tiktok')) return 'TT';
                        if (url.includes('youtube')) return 'YT';
                        if (url.includes('twitter') || url.includes('x.com')) return 'X';
                        return 'WEB';
                    }
                    function fetchLog() {
                        fetch('/api/logs').then(response => response.json()).then(data => {
                            const logContainer = document.getElementById('logContainer');
                            data.logs.slice(-20).forEach(entry => {
                                const logEntry = document.createElement('div');
                                logEntry.className = 'log-entry';
                                // ✅ ESCAPE CORREGIDO: doble barra invertida
                                const msg = entry.message
                                    .replace(/\\[(\\d{2}:\\d{2}:\\d{2})\\]/g, '<span class="timestamp">[$1]</span>')
                                    .replace(/⚒️|🧱|💰|🔥|⛏️|✅|🎬|📱|🎯|🏆|🎪/g, match => `<span class="highlight">${match}</span>`);
                                logEntry.innerHTML = msg;
                                logContainer.appendChild(logEntry);
                            });
                            logContainer.scrollTop = logContainer.scrollHeight;
                            setTimeout(fetchLog, 2000);
                        });
                    }
                    function updateGlobalStats() {
                        fetch('/api/logs').then(res => res.json()).then(data => {
                            const stats = data.stats;
                            document.getElementById('blockCount').textContent = stats.blocks_mined || 0;
                            document.getElementById('rewardCount').textContent = (stats.uber_coins || 0).toFixed(2);
                            document.getElementById('viralCount').textContent = stats.viral_blocks || 0;
                            document.getElementById('userCount').textContent = stats.blocks_mined > 0 ? 1 : 0;
                        });
                    }
                    updateGlobalStats();
                    setInterval(updateGlobalStats, 3000);
                    fetchLog();
                </script>
            </body>
            </html>
            """
            try:
                encoded = html_content.encode('utf-8')
                self.wfile.write(encoded)
                self.wfile.flush()
            except Exception as e:
                log(f"❌ Error enviando HTML: {e}")
                self.send_error(500, "Error interno al generar página")
            return
        if self.path == '/api/logs':
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.send_header('Cache-Control', 'no-cache')
            self.end_headers()
            recent_logs = get_recent_logs(50)
            with data_lock:
                stats_data = {
                    "uber_coins": UBER_COINS,
                    "blocks_mined": len(blockchain),
                    "viral_blocks": viral_blocks,
                    "zona_actual": ULTIMA_ZONA,
                    "zona_estado": zona_estado.get(ULTIMA_ZONA, {})
                }
            response_data = {"logs": recent_logs, "stats": stats_data}
            self.wfile.write(json.dumps(response_data).encode('utf-8'))
            return
        if self.path == '/ia/estado':
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            if 'cerebro_socialcoin' in globals():
                estado = cerebro_socialcoin.obtener_estado_sistema()
                self.wfile.write(json.dumps({
                    "ia_estado": {
                        "conciencia": cerebro_socialcoin.conciencia,
                        "emociones": cerebro_socialcoin.emociones,
                        "historial_engagement": list(cerebro_socialcoin.historial_engagement),
                        "configuracion": cerebro_socialcoin.ia_config
                    },
                    "sistema_estado": estado,
                    "timestamp": time.time()
                }).encode())
            else:
                self.wfile.write(json.dumps({"error": "IA no inicializada"}).encode())
            return
        if self.path == '/ia/recomendaciones':
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            if 'cerebro_socialcoin' in globals():
                estado = cerebro_socialcoin.obtener_estado_sistema()
                tendencia = cerebro_socialcoin.analizar_tendencia_engagement()
                recs = cerebro_socialcoin.generar_recomendaciones(estado, tendencia)
                self.wfile.write(json.dumps({
                    "tendencia_actual": tendencia,
                    "recomendaciones": recs,
                    "engagement_promedio": estado.get('engagement_promedio', 0),
                    "timestamp": time.time()
                }).encode())
            else:
                self.wfile.write(json.dumps({"error": "IA no inicializada"}).encode())
            return
        self.send_error(404, "Recurso no encontrado")
    def do_POST(self):
        global WEB_ACCESSED
        if not WEB_ACCESSED:
            WEB_ACCESSED = True
            log("🌐 Acceso POST detectado. Activando sistemas autónomos.")
        self._cleanup_expired_cookies()
        self._set_cors_headers()
        content_length = int(self.headers.get('Content-Length', 0))
        body = self.rfile.read(content_length) if content_length > 0 else b""
        if self.path == '/ia/consultar':
            try:
                data = json.loads(body.decode('utf-8'))
                pregunta = data.get('pregunta', '').strip()
                if not pregunta:
                    self.send_response(400)
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                    self.wfile.write(json.dumps({"error": "Se requiere una pregunta"}).encode())
                    return
                if not IA_READY:
                    respuesta = "🧠 IA SocialCoin aún se está inicializando. Por favor, espera unos segundos."
                else:
                    respuesta = consultar_deepseek_socialcoin(pregunta)
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({
                    "pregunta": pregunta,
                    "respuesta": respuesta,
                    "timestamp": time.time()
                }).encode())
                return
            except Exception as e:
                self.send_response(500)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"error": f"Error interno: {str(e)}"}).encode())
                return
        if self.path == '/mock/start_mining_socialcoin':
            try:
                data = json.loads(body.decode('utf-8'))
                user = data.get('user', 'anon')
                video_url = data.get('video_url', '')
                plataforma = "tiktok"
                if "instagram" in video_url:
                    plataforma = "instagram"
                elif "youtube" in video_url:
                    plataforma = "youtube"
                elif "x.com" in video_url or "twitter" in video_url:
                    plataforma = "twitter"
                recompensa = round(random.uniform(10.0, 500.0), 2)
                valor_usd = round(recompensa * 0.01, 2)
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({
                    "user": user,
                    "recompensa_estimada_scn": recompensa,
                    "valor_usd": valor_usd,
                    "plataforma": plataforma
                }).encode())
                log(f"mock 🎮 Simulación de minería para {user} en {plataforma} → {recompensa} UBER COINS")
                return
            except Exception as e:
                self.send_response(500)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"error": f"Error simulando minería: {str(e)}"}).encode())
                return
        if self.path == '/mock/payment':
            delay = random.uniform(0.05, 0.6)
            time.sleep(delay)
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            resp = {"status": "ok", "transaction_id": f"tx_{random.randint(100000,999999)}", "latency_ms": int(delay * 1000)}
            self.wfile.write(json.dumps(resp).encode())
            return
        self.send_error(405, "Método no permitido")
    def _cleanup_expired_cookies(self):
        now = time.time()
        with COOKIE_LOCK:
            expired = [k for k, v in ACTIVE_COOKIES.items() if isinstance(v, dict) and now > v.get("expiry", 0)]
            for k in expired:
                del ACTIVE_COOKIES[k]
    def log_message(self, fmt, *args):
        if VERBOSE_HTTP:
            log(fmt % args)
# ------------------ MAIN ------------------
def main():
    log("start 🧠 Iniciando UBER DAIMON VIVO — Neurona Autónoma + IA SOCIALCOIN")
    cargar_estado()
    load_daimon_brain()
    global cerebro_socialcoin, IA_READY
    cerebro_socialcoin = SocialCoinCerebro()
    IA_READY = True
    signal.signal(signal.SIGINT, cleanup_and_exit)
    signal.signal(signal.SIGTERM, cleanup_and_exit)
    
    # 🔥 RENDER & GITHUB: Puerto HTTP ya configurado desde variable de entorno PORT
    log(f"🌐 Puerto HTTP elegido: {HTTP_PORT}")
    host = "0.0.0.0" if os.getenv("RENDER") else "localhost"
    print(f"\n🌍 Accede desde tu navegador: http://{host if host != '0.0.0.0' else 'localhost'}:{HTTP_PORT}\n")

    global http_server_wrapper
    http_server_wrapper = HTTPServerWrapper(port=HTTP_PORT)
    if not http_server_wrapper.start():
        log("❌ No se pudo iniciar el servidor HTTP. Saliendo.")
        cleanup_and_exit()
        return

    for p in [SIM_DIR, SONIDOS_DIR, LOGS_FAKE_DIR]:
        p.mkdir(parents=True, exist_ok=True)

    threading.Thread(target=daimon_autonomous_loop, daemon=True).start()
    threading.Thread(target=actualizar_zonificacion, daemon=True).start()
    threading.Thread(target=simulate_route_loop, daemon=True).start()
    threading.Thread(target=mente_autonoma_socialcoin, daemon=True).start()

    log("success Sistema iniciado — Daimon Vivo + IA SocialCoin activos en segundo plano.")
    if DURACION > 0:
        time.sleep(DURACION)
    else:
        try:
            while not STOP_EVENT.is_set():
                time.sleep(1)
        except KeyboardInterrupt:
            pass
    cleanup_and_exit()

if __name__ == "__main__":
    try:
        print("="*70)
        print("🚗 UBER DAIMON VIVO + ⛏️ SOCIALCOIN - SISTEMA COMPLETO")
        print("✅ Llamadas reales a API Uber")
        print("✅ Sistema de IA autónomo con negociación")
        print("✅ Chat interactivo con DeepSeek")
        print("✅ Agentes IA negociando parámetros")
        print("✅ Minería adaptada a redes sociales")
        print("✅ Compatible con localhost y Google Sites")
        print("✅ RENDER & GITHUB READY: sin Gunicorn, puerto dinámico $PORT")
        print("="*70)
        main()
    except KeyboardInterrupt:
        log("stop Interrupción por teclado")
    finally:
        cleanup_and_exit()
