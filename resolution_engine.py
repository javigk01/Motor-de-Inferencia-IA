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

# ---------- algoritmo principal (cadena desde negación-meta) ----------
def refutacion_cadena(base_clausulas: List[List[str]], meta: str, verbose: bool=True) -> bool:
    """
    base_clausulas: lista de cláusulas (cada cláusula es lista de literales strings)
    meta: string con la meta, ejemplo "Odia(Marco,Cesar)"
    retorna True si demuestra la meta (llega a ⊥), False si no.
    """
    # preparar
    kb = [list(c) for c in base_clausulas]
    neg_meta = f"¬{meta}" if not meta.startswith("¬") else meta[1:]
    actual = [neg_meta]
    vistos: Set[Tuple[str,...]] = set()
    paso = 1

    if verbose:
        print("=== Resolución por refutación (cadena desde la negación-meta) ===\n")
        print("Base de conocimiento:")
        for i, c in enumerate(kb, 1):
            print(f" {i}. {' ∨ '.join(c)}")
        print(f"\nMeta a probar: {meta}")
        print(f"Negación-meta (inicial): {neg_meta}\n")
        print("---------------------------------------------------------------")

    # bucle: tomamos la cláusula 'actual' y la resolvemos contra las cláusulas de la KB en orden
    while True:
        key_actual = clausula_to_key(actual)
        if key_actual in vistos:
            if verbose:
                print(f"\n🔁 Clausula actual ya vista: {actual}. No hay avance posible -> NO demostrable.")
            return False
        vistos.add(key_actual)

        if verbose:
            print(f"\n🧩 Etapa {paso}")
            print(f" Cláusula actual: { ' ∨ '.join(actual) }")

        progreso = False
        # intentamos resolver con cada cláusula de la KB (en orden)
        for idx, claus in enumerate(kb, start=1):
            intento = resolver_actual_con_base(actual, claus)
            if intento is None:
                if verbose:
                    print(f"  - No se puede resolver con KB[{idx}]: { ' ∨ '.join(claus) }")
                continue
            resolvente, subst, literal_cancelado = intento
            if verbose:
                print(f"  → Resuelto con KB[{idx}]: { ' ∨ '.join(claus) }")
                print(f"    Literales cancelados: {literal_cancelado}")
                if subst:
                    print(f"    Sustitución: {subst}")
                print(f"    Resultado (resolvente): { ' ∨ '.join(resolvente) if resolvente else '⊥ (cláusula vacía)'}")
            # si resolvente es vacía -> éxito
            if not resolvente:
                if verbose:
                    print("\n✅ Se alcanzó la cláusula vacía (⊥). Contradicción encontrada.")
                    print(f"⇒ La meta {meta} se demuestra.")
                return True
            # si el resolvente es nuevo y no tautológico, lo tomamos como nueva 'actual' y continuamos la cadena
            actual = resolvente
            progreso = True
            paso += 1
            break  # importante: tomamos solo la primera resolución aplicable y continuamos la cadena

        if not progreso:
            if verbose:
                print("\n⚠️ No se encontró ninguna cláusula de la KB con la que resolver la cláusula actual.")
                print("⇒ No se pudo continuar la cadena desde la negación de la meta.")
            return False

# ---------- ejemplo (la misma base de la imagen, con cláusula 6 ya corregida) ----------
if __name__ == "__main__":
    base = [
        ["Hombre(Marco)"],
        ["Pompeyano(Marco)"],
        ["¬Pompeyano(x)", "Romano(x)"],
        ["Gobernante(Cesar)"],
        ["¬Romano(x)", "Leal(x,Cesar)", "Odia(x,Cesar)"],
        # cláusula 6 corregida con ¬Leal(x,y) como literal negativo
        ["¬Hombre(x)", "¬Gobernante(y)", "¬IntentaAsesinar(x,y)", "¬Leal(x,y)"],
        ["IntentaAsesinar(Marco,Cesar)"]
    ]

    meta = "Odia(Marco,Cesar)"
    resultado = refutacion_cadena(base, meta, verbose=True)
    print("\n---------------------------------------------------------------")
    print("Resultado final:", "SE PUEDE DEMOSTRAR" if resultado else "NO SE PUEDE DEMOSTRAR")
