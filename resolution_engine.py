#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Resolución por refutación - Procedimiento automático en cadena
Parte desde la negación de la meta y en cada paso resuelve la cláusula actual
con alguna cláusula de la base (en orden) hasta llegar a ⊥ o no poder avanzar.
Evita bucles registrando cláusulas ya vistas.
"""

import re
from typing import List, Tuple, Dict, Optional, Set

# ---------- utilidades de parseo y representación ----------
def parse_literal(lit: str) -> Tuple[bool, str, List[str]]:
    """
    Devuelve (negado, predicado, [args])
    Ej: "¬Odia(x,Cesar)" -> (True, "Odia", ["x","Cesar"])
    """
    s = lit.strip()
    neg = False
    if s.startswith("¬"):
        neg = True
        s = s[1:].strip()
    m = re.match(r"^([A-Za-z_]\w*)\s*(?:\((.*)\))?$", s)
    if not m:
        raise ValueError(f"Literal inválido: {lit}")
    pred = m.group(1)
    args = []
    if m.group(2):
        args = [a.strip() for a in m.group(2).split(",")]
    return neg, pred, args

def lit_to_str(neg: bool, pred: str, args: List[str]) -> str:
    if args:
        inner = ",".join(args)
        return ( "¬" if neg else "" ) + f"{pred}({inner})"
    else:
        return ( "¬" if neg else "" ) + pred

def clausula_to_key(clausula: List[str]) -> Tuple[str,...]:
    # representación canónica (ordenada) para comparación en 'vistos'
    return tuple(sorted([s.strip() for s in clausula]))

# ---------- unificación simple (variables minúsculas) ----------
def unificar_args(a: str, b: str, subst: Dict[str,str]) -> Optional[Dict[str,str]]:
    """Unifica dos términos (variables o constantes) con sustitución previa subst."""
    # si iguales -> ok
    if a == b:
        return subst
    # si a es variable (minúscula inicial)
    if a and a[0].islower():
        # ocurre ocurre: verificar occurs check simple omitido por simplicidad
        if a in subst:
            return unificar_args(subst[a], b, subst)
        else:
            subst2 = subst.copy()
            subst2[a] = b
            return subst2
    if b and b[0].islower():
        if b in subst:
            return unificar_args(a, subst[b], subst)
        else:
            subst2 = subst.copy()
            subst2[b] = a
            return subst2
    # dos constantes distintas -> falla
    return None

def unificar_lit(lpos: Tuple[bool,str,List[str]], lneg: Tuple[bool,str,List[str]]) -> Optional[Dict[str,str]]:
    """
    Intenta unificar lit_pos (positvo) con lit_neg (positivo form, la versión contraria ya retirada la negación).
    Devuelve sustitución o None.
    """
    neg1, pred1, args1 = lpos
    neg2, pred2, args2 = lneg
    if pred1 != pred2 or len(args1) != len(args2):
        return None
    subst: Dict[str,str] = {}
    for a, b in zip(args1, args2):
        subst = unificar_args(a, b, subst)
        if subst is None:
            return None
    return subst

def aplicar_subst_literal(literal: str, subst: Dict[str,str]) -> str:
    neg, pred, args = parse_literal(literal)
    if not args:
        return lit_to_str(neg, pred, args)
    new_args = [subst.get(a, a) for a in args]
    return lit_to_str(neg, pred, new_args)

def aplicar_subst_clausula(clausula: List[str], subst: Dict[str,str]) -> List[str]:
    return list({ aplicar_subst_literal(l, subst) for l in clausula })  # set para evitar duplicados

# ---------- resolver cláusula actual contra una cláusula de la base ----------
def resolver_actual_con_base(actual: List[str], base: List[str]) -> Optional[Tuple[List[str], Dict[str,str], str]]:
    """
    Intenta resolver 'actual' con 'base'.
    Si encuentra un par complementario y unificación exitosa:
      retorna (resolvente_lista, sustitucion, literal_cancelado_representacion)
    Si no se puede, retorna None.
    Se intenta cada par de literales complementarios en orden.
    """
    for la in actual:
        neg_a, pred_a, args_a = parse_literal(la)
        for lb in base:
            neg_b, pred_b, args_b = parse_literal(lb)
            # buscamos complementarios (uno negado y otro positivo y mismo predicado)
            if pred_a != pred_b:
                continue
            if neg_a == neg_b:
                continue
            # definamos lit_pos (sin ¬) y lit_other
            if neg_a:
                lit_pos = (False, pred_a, args_a)
                lit_other = (False, pred_b, args_b)  # lb pos form
                # unificar lit_pos con lit_other (pero con variables)
                subst = unificar_lit(lit_pos, lit_other)
                literal_cancelado = f"{la} ↔ {lb}"
            else:
                lit_pos = (False, pred_a, args_a)
                lit_other = (False, pred_b, args_b)
                subst = unificar_lit(lit_pos, lit_other)
                literal_cancelado = f"{la} ↔ {lb}"
            if subst is not None:
                # aplicar sustitución a ambas cláusulas y formar resolvente quitando los dos literales
                c1_sub = aplicar_subst_clausula(actual, subst)
                c2_sub = aplicar_subst_clausula(base, subst)
                # quitar los literales cancelados (aplicados)
                la_ap = aplicar_subst_literal(la, subst)
                lb_ap = aplicar_subst_literal(lb, subst)
                resolvente = [lit for lit in (c1_sub + c2_sub) if lit != la_ap and lit != lb_ap]
                # eliminar tautologías sencillas (p, ¬p en misma cláusula)
                # representaremos negación por prefijo '¬'
                res_set = set(resolvente)
                # si contiene p y ¬p -> tautología, podemos ignorarla (no útil)
                removed = False
                for lit in list(res_set):
                    if lit.startswith("¬"):
                        if lit[1:] in res_set:
                            # tautología -> descartamos este resolvente
                            removed = True
                            break
                if removed:
                    continue
                # orden y retorno
                return sorted(list(set(resolvente))), subst, literal_cancelado
    return None

# ---------- algoritmo principal (resolución general - no lineal) ----------
def refutacion_general(base_clausulas: List[List[str]], meta: str, verbose: bool=True) -> bool:
    """
    Algoritmo de resolución general (no lineal).
    Añade cada resolvente a la base de conocimiento y prueba todas las combinaciones.
    base_clausulas: lista de cláusulas (cada cláusula es lista de literales strings)
    meta: string con la meta, ejemplo "Odia(Marco,Cesar)"
    retorna True si demuestra la meta (llega a ⊥), False si no.
    """
    # preparar: agregar negación de la meta a la base
    kb = [list(c) for c in base_clausulas]
    neg_meta = f"¬{meta}" if not meta.startswith("¬") else meta[1:]
    kb.append([neg_meta])
    
    vistos: Set[Tuple[str,...]] = set()
    for c in kb:
        vistos.add(clausula_to_key(c))
    
    if verbose:
        print("=== Resolución por refutación (algoritmo general) ===\n")
        print("Base de conocimiento inicial:")
        for i, c in enumerate(kb[:-1], 1):
            print(f" {i}. {' ∨ '.join(c)}")
        print(f"\nMeta a probar: {meta}")
        print(f"Negación-meta agregada: {neg_meta}")
        print(f" {len(kb)}. {' ∨ '.join(kb[-1])}")
        print("\n---------------------------------------------------------------")
    
    paso = 1
    nuevas_clausulas = []
    
    # Mientras haya cláusulas por resolver
    while True:
        if verbose:
            print(f"\n� Paso {paso}: Intentando resolver todas las combinaciones de cláusulas...")
        
        encontro_resolvente = False
        
        # Probar todas las combinaciones de pares de cláusulas
        for i in range(len(kb)):
            for j in range(i + 1, len(kb)):
                claus1 = kb[i]
                claus2 = kb[j]
                
                # Intentar resolver estas dos cláusulas
                intento = resolver_actual_con_base(claus1, claus2)
                if intento is None:
                    continue
                
                resolvente, subst, literal_cancelado = intento
                key_resolvente = clausula_to_key(resolvente)
                
                # Si ya vimos este resolvente, saltar
                if key_resolvente in vistos:
                    continue
                
                encontro_resolvente = True
                
                if verbose:
                    print(f"\n  ✨ Nueva resolución encontrada:")
                    print(f"     Cláusula 1: {' ∨ '.join(claus1)}")
                    print(f"     Cláusula 2: {' ∨ '.join(claus2)}")
                    print(f"     Literales cancelados: {literal_cancelado}")
                    if subst:
                        print(f"     Sustitución: {subst}")
                    print(f"     Resolvente: { ' ∨ '.join(resolvente) if resolvente else '⊥ (cláusula vacía)'}")
                
                # Si resolvente es vacía -> éxito
                if not resolvente:
                    if verbose:
                        print("\n✅ Se alcanzó la cláusula vacía (⊥). Contradicción encontrada.")
                        print(f"⇒ La meta {meta} se demuestra.")
                    return True
                
                # Agregar el resolvente a la lista de nuevas cláusulas
                nuevas_clausulas.append(resolvente)
                vistos.add(key_resolvente)
        
        # Si no se encontraron nuevos resolventes, terminar
        if not encontro_resolvente:
            if verbose:
                print("\n⚠️ No se pueden generar más resolventes.")
                print("⇒ No se puede demostrar la meta.")
            return False
        
        # Añadir todas las nuevas cláusulas a la base de conocimiento
        if verbose:
            print(f"\n  📝 Se agregaron {len(nuevas_clausulas)} nueva(s) cláusula(s) a la base de conocimiento.")
        
        kb.extend(nuevas_clausulas)
        nuevas_clausulas = []
        paso += 1

# ---------- funciones para leer desde archivos ----------
def leer_base_conocimientos(archivo: str) -> List[List[str]]:
    """
    Lee la base de conocimientos desde un archivo de texto.
    Formato esperado:
    - Una cláusula por línea
    - Literales separados por '∨' o 'v' o '|'
    - Líneas vacías o que empiecen con '#' se ignoran
    """
    base = []
    try:
        with open(archivo, 'r', encoding='utf-8') as f:
            for linea in f:
                linea = linea.strip()
                # Ignorar líneas vacías o comentarios
                if not linea or linea.startswith('#'):
                    continue
                
                # Separar literales por ∨, v, o |
                literales = re.split(r'[∨v|]', linea)
                clausula = [lit.strip() for lit in literales if lit.strip()]
                if clausula:
                    base.append(clausula)
    except FileNotFoundError:
        print(f"❌ Error: No se encontró el archivo {archivo}")
        return []
    except Exception as e:
        print(f"❌ Error al leer el archivo {archivo}: {e}")
        return []
    
    return base

def leer_meta(archivo: str) -> str:
    """
    Lee la meta desde un archivo de texto.
    El archivo debe contener solo la meta en una línea.
    """
    try:
        with open(archivo, 'r', encoding='utf-8') as f:
            meta = f.read().strip()
            return meta
    except FileNotFoundError:
        print(f"❌ Error: No se encontró el archivo {archivo}")
        return ""
    except Exception as e:
        print(f"❌ Error al leer el archivo {archivo}: {e}")
        return ""

def crear_archivo_ejemplo():
    """Crea archivos de ejemplo para demostrar el uso"""
    # Crear archivo de base de conocimientos
    base_contenido = """# Base de conocimientos - Ejemplo Marco/César
# Una cláusula por línea, literales separados por ∨

Hombre(Marco)
Pompeyano(Marco)
¬Pompeyano(x) ∨ Romano(x)
Gobernante(Cesar)
¬Romano(x) ∨ Leal(x,Cesar) ∨ Odia(x,Cesar)
¬Hombre(x) ∨ ¬Gobernante(y) ∨ ¬IntentaAsesinar(x,y) ∨ ¬Leal(x,y)
IntentaAsesinar(Marco,Cesar)"""
    
    with open('base_conocimientos.txt', 'w', encoding='utf-8') as f:
        f.write(base_contenido)
    
    # Crear archivo de meta
    with open('meta.txt', 'w', encoding='utf-8') as f:
        f.write('Odia(Marco,Cesar)')
    
    print("✅ Archivos de ejemplo creados:")
    print("   - base_conocimientos.txt")
    print("   - meta.txt")

# ---------- ejemplo desde archivos ----------
if __name__ == "__main__":
    import sys
    
    # Si se pasan argumentos, usar archivos específicos
    if len(sys.argv) >= 3:
        archivo_base = sys.argv[1]
        archivo_meta = sys.argv[2]
    else:
        # Usar archivos por defecto y crearlos si no existen
        archivo_base = 'base_conocimientos.txt'
        archivo_meta = 'meta.txt'
        
        # Verificar si existen, si no, crearlos
        import os
        if not os.path.exists(archivo_base) or not os.path.exists(archivo_meta):
            print("📝 Creando archivos de ejemplo...")
            crear_archivo_ejemplo()
            print()
    
    print(f"📁 Leyendo base de conocimientos desde: {archivo_base}")
    base = leer_base_conocimientos(archivo_base)
    
    print(f"🎯 Leyendo meta desde: {archivo_meta}")
    meta = leer_meta(archivo_meta)
    
    if not base or not meta:
        print("❌ Error: No se pudo leer la base de conocimientos o la meta")
        sys.exit(1)
    
    print(f"\n📚 Base de conocimientos cargada ({len(base)} cláusulas)")
    print(f"🎯 Meta a demostrar: {meta}")
    print("\n" + "="*60)
    
    resultado = refutacion_general(base, meta, verbose=True)
    print("\n" + "="*60)
    print("🏆 Resultado final:", "✅ SE PUEDE DEMOSTRAR" if resultado else "❌ NO SE PUEDE DEMOSTRAR")
