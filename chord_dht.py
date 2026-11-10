#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Chord DHT - simulation d'un réseau overlay en anneau (Stoica et al., SIGCOMM'01)

Fonctionnalités (menu) :
  1. Création de l'anneau (m bits, identifiants = SHA-1 tronqué à m bits) + pairs initiaux
  2. Join d'un pair (affichage de sa finger table)
  3. Lookup d'une clé k à partir des finger tables (trace des sauts)
  4. Départ d'un pair (mise à jour des finger tables)
  5. Affichage de l'anneau, des pairs et des finger tables
  6. Arrivées / départs de p pairs en concurrence (threads + stabilisation)
  7. Insertion d'une donnée (clé/valeur)   8. Vérification de cohérence

Deux modes de maintenance, comme dans le papier :
  - séquentiel (Fig. 6) : init_finger_table / update_others / update_finger_table
  - concurrent (Fig. 7) : join + stabilize / notify / fix_fingers périodiques,
    liste de successeurs pour tolérer les départs simultanés.

Un identifiant peut être donné directement avec la notation  #5  (utile pour
reproduire l'exemple m=3 du papier : nœuds #0 #1 #3).

Usage :  python3 chord_dht.py            (menu interactif)
         python3 chord_dht.py --demo     (scénario automatique)
         python3 chord_dht.py --selftest (tests aléatoires)
"""
import hashlib
import random
import sys
import threading
import time
from bisect import bisect_left


class NodeFailed(Exception):
    pass


class LookupFailed(Exception):
    pass


# ----------------------------------------------------------------------------
# Arithmétique sur le cercle d'identifiants (modulo 2^m)
# ----------------------------------------------------------------------------
def sha1_m(text, m):
    """Identifiant m bits : SHA-1 du texte, réduit modulo 2^m."""
    return int(hashlib.sha1(text.encode("utf-8")).hexdigest(), 16) % (2 ** m)


def in_oo(x, a, b):
    """x dans l'intervalle circulaire ]a, b[ (si a == b : tout sauf a)."""
    if a < b:
        return a < x < b
    if a > b:
        return x > a or x < b
    return x != a


def in_oc(x, a, b):
    """x dans ]a, b] (si a == b : tout le cercle)."""
    if a == b:
        return True
    if a < b:
        return a < x <= b
    return x > a or x <= b


def in_co(x, a, b):
    """x dans [a, b[ (si a == b : intervalle vide)."""
    if a == b:
        return False
    if a < b:
        return a <= x < b
    return x >= a or x < b


# ----------------------------------------------------------------------------
# Nœud Chord
# ----------------------------------------------------------------------------
class Node:
    def __init__(self, ring, nid, name):
        self.ring = ring
        self.id = nid
        self.name = name
        self.m = ring.m
        self.start = [(nid + 2 ** i) % ring.M for i in range(ring.m)]
        self.finger = [self] * ring.m          # finger[i] = successeur de start[i]
        self.predecessor = None
        self.succ_list = []
        self.keys = {}                          # id -> (étiquette, valeur)
        self.alive = True
        self.lock = threading.RLock()

    # successeur = premier finger
    @property
    def successor(self):
        return self.finger[0]

    def __repr__(self):
        return f"Node({self.id})"

    # ---------------------------------------------------------------- routage
    def live_successor(self):
        s = self.finger[0]
        if s.alive:
            return s
        for z in list(self.succ_list):
            if z.alive:
                self.finger[0] = z
                return z
        best, bd = None, None
        for f in self.finger:
            if f.alive and f is not self:
                d = (f.id - self.id) % self.ring.M
                if bd is None or d < bd:
                    best, bd = f, d
        if best is not None:
            self.finger[0] = best
            return best
        return self

    def closest_preceding_finger(self, key):
        idx = self.closest_preceding_index(key)
        return self if idx is None else self.finger[idx]

    def closest_preceding_index(self, key):
        for i in range(self.m - 1, -1, -1):
            f = self.finger[i]
            if f.alive and in_oo(f.id, self.id, key):
                return i
        return None

    def find_predecessor(self, key, trace=None):
        n = self
        limit = 64 + 4 * self.m + 2 * len(self.ring.nodes)
        hops = 0
        while True:
            s = n.live_successor()
            if in_oc(key, n.id, s.id):
                return n
            idx = n.closest_preceding_index(key)
            if idx is None:
                return n
            nxt = n.finger[idx]
            if trace is not None:
                trace.append((n, idx, nxt))
            n = nxt
            hops += 1
            if hops > limit:
                raise LookupFailed(f"trop de sauts pour la clé {key}")

    def find_successor(self, key, trace=None):
        p = self.find_predecessor(key, trace)
        return p.live_successor()

    # ------------------------------------------- mode séquentiel (papier Fig.6)
    def join_seq(self, boot):
        if boot is None:
            self.finger = [self] * self.m
            self.predecessor = self
            return
        self.init_finger_table(boot)
        self.update_others()
        self.take_keys_from_successor()

    def init_finger_table(self, boot):
        self.finger[0] = boot.find_successor(self.start[0])
        succ = self.finger[0]
        self.predecessor = succ.predecessor
        succ.predecessor = self
        self.predecessor.finger[0] = self
        for i in range(self.m - 1):
            if in_co(self.start[i + 1], self.id, self.finger[i].id):
                self.finger[i + 1] = self.finger[i]
            else:
                self.finger[i + 1] = boot.find_successor(self.start[i + 1])

    def update_others(self):
        M = self.ring.M
        for i in range(self.m):
            ident = (self.id - 2 ** i) % M
            p = self.find_predecessor(ident)
            if p.successor.id == ident and p.successor is not self:
                p = p.successor          # un nœud situé exactement en n - 2^i
            if p is not self:
                p.update_finger_table(self, i)

    def update_finger_table(self, s, i):
        p = self
        while p is not s and in_co(s.id, p.start[i], p.finger[i].id):
            p.finger[i] = s
            p = p.predecessor

    def take_keys_from_successor(self):
        succ = self.successor
        if succ is self:
            return
        moving = {k: v for k, v in succ.keys.items()
                  if not in_oc(k, self.id, succ.id)}
        for k in moving:
            del succ.keys[k]
        self.keys.update(moving)

    def leave_seq(self):
        succ, pred = self.successor, self.predecessor
        M = self.ring.M
        succ.keys.update(self.keys)
        self.keys = {}
        for i in range(self.m):
            ident = (self.id - 2 ** i) % M
            p = self.find_predecessor(ident)
            if p.successor.id == ident and p.successor is not self:
                p = p.successor
            if p is self:
                p = self.predecessor
            while p is not self and p.finger[i] is self:
                p.finger[i] = succ
                p = p.predecessor
        pred.finger[0] = succ
        succ.predecessor = pred
        self.alive = False

    # ------------------------------------------- mode concurrent (papier Fig.7)
    def join_conc(self, boot):
        self.predecessor = None
        s = boot.find_successor(self.id)
        self.finger = [s] * self.m

    def stabilize(self):
        s = self.live_successor()
        x = s.predecessor
        if x is not None and x.alive and in_oo(x.id, self.id, s.id):
            s = x
            self.finger[0] = x
        s.notify(self)
        lst = [s] + [z for z in s.succ_list if z is not self and z is not s]
        self.succ_list = lst[: self.ring.r]

    def notify(self, n):
        changed = False
        with self.lock:
            p = self.predecessor
            if p is None or not p.alive or in_oo(n.id, p.id, self.id):
                changed = p is not n
                self.predecessor = n
        if changed and n is not self:
            self.hand_keys_to(n)

    def hand_keys_to(self, pred):
        with self.lock:
            moving = {k: v for k, v in self.keys.items()
                      if not in_oc(k, pred.id, self.id)}
            for k in moving:
                del self.keys[k]
        if moving:
            with pred.lock:
                pred.keys.update(moving)

    def check_predecessor(self):
        p = self.predecessor
        if p is not None and not p.alive:
            self.predecessor = None

    def fix_fingers(self):
        for i in range(self.m):
            try:
                self.finger[i] = self.find_successor(self.start[i])
            except LookupFailed:
                pass

    def heal(self):
        """Détection/réparation de partition (Section 7 du papier) : on demande
        à un nœud d'amorçage connu de résoudre l'identifiant qui suit le nôtre."""
        others = [n for n in list(self.ring.nodes.values())
                  if n.alive and n is not self]
        if not others:
            return
        s = random.choice(others).find_successor((self.id + 1) % self.ring.M)
        cur = self.live_successor()
        if s.alive and s is not self and (cur is self or in_oo(s.id, self.id, cur.id)):
            self.finger[0] = s

    def stabilize_round(self, heal=False):
        try:
            self.check_predecessor()
            if heal or self.live_successor() is self:
                self.heal()
            self.stabilize()
            self.fix_fingers()
        except (LookupFailed, NodeFailed, RecursionError):
            pass

    def leave_conc(self):
        """Départ volontaire : les clés passent au 1er successeur vivant."""
        with self.lock:
            keys, self.keys = self.keys, {}
            self.alive = False
        cands = [self.finger[0]] + list(self.succ_list)
        for c in cands:
            if c is self:
                continue
            with c.lock:
                if c.alive:
                    c.keys.update(keys)
                    return
        other = self.ring.any_alive(exclude=self)
        if other is not None:
            with other.lock:
                other.keys.update(keys)


# ----------------------------------------------------------------------------
# Anneau
# ----------------------------------------------------------------------------
class Ring:
    def __init__(self, m):
        if not 1 <= m <= 160:
            raise ValueError("m doit être compris entre 1 et 160")
        self.m = m
        self.M = 2 ** m
        self.nodes = {}                  # id -> Node (nœuds vivants)
        self.lock = threading.RLock()
        self.counter = 0
        self.r = max(3, min(m, 8))       # taille de la liste de successeurs

    # ---- identifiants
    def make_id(self, name):
        if name.startswith("#"):
            v = int(name[1:])
            if not 0 <= v < self.M:
                raise ValueError(f"identifiant hors de [0, {self.M - 1}]")
            return v
        return sha1_m(name, self.m)

    def new_node(self, name):
        nid = self.make_id(name)
        with self.lock:
            if nid in self.nodes:
                raise ValueError(
                    f"collision : l'identifiant {nid} est déjà pris par "
                    f"'{self.nodes[nid].name}'")
            n = Node(self, nid, name)
            self.nodes[nid] = n
        return n

    def free_name(self):
        """Génère un nom 'peerN' dont l'identifiant est libre."""
        if len(self.nodes) >= self.M:
            raise ValueError("l'anneau est plein")
        while True:
            self.counter += 1
            name = f"peer{self.counter}"
            if self.make_id(name) not in self.nodes:
                return name

    def sorted_nodes(self):
        return [self.nodes[i] for i in sorted(self.nodes)]

    def any_alive(self, exclude=None):
        for n in list(self.nodes.values()):
            if n.alive and n is not exclude:
                return n
        return None

    def resolve(self, token):
        token = token.strip()
        if not token:
            return None
        if token.startswith("#") and token[1:].isdigit():
            return self.nodes.get(int(token[1:]))
        if token.isdigit() and int(token) in self.nodes:
            return self.nodes[int(token)]
        for n in self.nodes.values():
            if n.name == token:
                return n
        try:
            return self.nodes.get(self.make_id(token))
        except ValueError:
            return None

    # ---- opérations séquentielles
    def join(self, name, boot=None):
        n = self.new_node(name)
        try:
            if len(self.nodes) == 1:
                n.join_seq(None)
            else:
                if boot is None:
                    boot = next(x for x in self.nodes.values() if x is not n)
                n.join_seq(boot)
        except Exception:
            del self.nodes[n.id]
            raise
        self.refresh_succ_lists()
        return n

    def leave(self, node):
        if len(self.nodes) == 1:
            node.alive = False
            del self.nodes[node.id]
            return
        node.leave_seq()
        del self.nodes[node.id]
        self.refresh_succ_lists()

    def refresh_succ_lists(self):
        for n in self.nodes.values():
            lst, cur = [], n
            for _ in range(self.r):
                cur = cur.successor
                if cur is n:
                    break
                lst.append(cur)
            n.succ_list = lst

    # ---- clés
    def key_id(self, label):
        return self.make_id(label) if label.startswith("#") else sha1_m(label, self.m)

    def insert(self, start, label, value):
        kid = self.key_id(label)
        owner = start.find_successor(kid)
        with owner.lock:
            owner.keys[kid] = (label, value)
        return kid, owner

    def redistribute_keys(self):
        moved = 0
        for n in list(self.nodes.values()):
            for k in list(n.keys):
                try:
                    owner = n.find_successor(k)
                except LookupFailed:
                    continue
                if owner is not n and k in n.keys:
                    owner.keys[k] = n.keys.pop(k)
                    moved += 1
        return moved

    # ---- vérification par rapport à la « vérité terrain »
    def verify(self, check_keys=True):
        nodes = self.sorted_nodes()
        n = len(nodes)
        errors = []
        if n == 0:
            return True, errors
        ids = [x.id for x in nodes]

        def truth(x):
            return nodes[bisect_left(ids, x) % n]

        for idx, nd in enumerate(nodes):
            if nd.successor is not nodes[(idx + 1) % n]:
                errors.append(f"successeur de {nd.id} incorrect")
            if nd.predecessor is not nodes[idx - 1]:
                errors.append(f"prédécesseur de {nd.id} incorrect")
            for i in range(self.m):
                if nd.finger[i] is not truth(nd.start[i]):
                    errors.append(f"finger[{i}] de {nd.id} incorrect")
                    break
            if check_keys:
                for k in nd.keys:
                    if truth(k) is not nd:
                        errors.append(f"clé {k} mal placée sur {nd.id}")
        return not errors, errors

    # ---- concurrence
    def stabilize_until_consistent(self, max_rounds=60, verbose=True):
        for rnd in range(1, max_rounds + 1):
            threads = [threading.Thread(target=nd.stabilize_round,
                                        kwargs={"heal": rnd > 4})
                       for nd in list(self.nodes.values())]
            random.shuffle(threads)
            for t in threads:
                t.start()
            for t in threads:
                t.join()
            ok, _ = self.verify(check_keys=False)
            if ok:
                if verbose:
                    print(f"  stabilisation : cohérent après {rnd} ronde(s)")
                break
        else:
            if verbose:
                print("  stabilisation : non convergé (essayez de relancer)")
            return False
        moved = self.redistribute_keys()
        if verbose and moved:
            print(f"  {moved} clé(s) replacée(s) sur leur nœud responsable")
        return True

    def concurrent_ops(self, join_names, leavers, verbose=True):
        """p arrivées et q départs exécutés simultanément (threads)."""
        survivors = [n for n in self.nodes.values() if n not in leavers]
        if not survivors and join_names:
            raise ValueError("aucun nœud survivant pour servir de point d'entrée")
        joiners = [self.new_node(nm) for nm in join_names]
        total = len(joiners) + len(leavers)
        barrier = threading.Barrier(total) if total else None
        errors = []

        def do_join(nd):
            barrier.wait()
            try:
                nd.join_conc(random.choice(survivors))
            except Exception as e:           # noqa
                errors.append((nd, e))

        def do_leave(nd):
            barrier.wait()
            nd.leave_conc()

        ths = [threading.Thread(target=do_join, args=(j,)) for j in joiners]
        ths += [threading.Thread(target=do_leave, args=(l,)) for l in leavers]
        for t in ths:
            t.start()
        for t in ths:
            t.join()
        with self.lock:
            for l in leavers:
                self.nodes.pop(l.id, None)
        for nd, e in errors:
            print(f"  ! join de {nd.id} a échoué : {e}")
        if verbose:
            print(f"  {len(joiners)} arrivée(s) et {len(leavers)} départ(s) "
                  f"simultanés exécutés ; stabilisation…")
        return self.stabilize_until_consistent(verbose=verbose)


# ----------------------------------------------------------------------------
# Affichage
# ----------------------------------------------------------------------------
def fmt(ring, x):
    if x is None:
        return "-"
    return str(x) if ring.m <= 16 else f"{x:x}"[:8] + "…"


def show_finger_table(n, ring=None):
    ring = ring or n.ring
    f = lambda x: fmt(ring, x)
    pred = n.predecessor.id if n.predecessor else None
    print(f"Nœud {f(n.id)} ('{n.name}')  prédécesseur={f(pred)}  "
          f"successeur={f(n.successor.id)}")
    print(f"  clés stockées : "
          f"{', '.join(f'{f(k)}[{v[0]}]' for k, v in sorted(n.keys.items())) or '(aucune)'}")
    print("  i | start | intervalle        | successeur")
    print("  --+-------+-------------------+-----------")
    m = ring.m
    if m <= 16:
        for i in range(m):
            nxt = n.start[i + 1] if i + 1 < m else n.id
            print(f"  {i:<2}| {f(n.start[i]):<6}| [{f(n.start[i])},{f(nxt)}){'':<{max(1, 12 - len(f(n.start[i])) - len(f(nxt)))}}| {f(n.finger[i].id)}")
    else:
        i = 0
        while i < m:
            j = i
            while j + 1 < m and n.finger[j + 1] is n.finger[i]:
                j += 1
            rg = f"{i}" if i == j else f"{i}..{j}"
            print(f"  {rg:<6}| start={f(n.start[i])} | successeur {f(n.finger[i].id)}")
            i = j + 1


def show_ring(ring, with_fingers=True):
    nodes = ring.sorted_nodes()
    if not nodes:
        print("(anneau vide)")
        return
    f = lambda x: fmt(ring, x)
    print(f"\n=== Anneau Chord : m={ring.m} (espace 2^{ring.m} = {ring.M if ring.m <= 40 else '…'}), "
          f"{len(nodes)} pair(s) ===")
    print("  " + " → ".join(f(n.id) for n in nodes) + f" → ({f(nodes[0].id)})")
    for n in nodes:
        print()
        if with_fingers:
            show_finger_table(n, ring)
        else:
            print(f"Nœud {f(n.id)} ('{n.name}') succ={f(n.successor.id)}")


def lookup(ring, start, label):
    kid = ring.key_id(label)
    f = lambda x: fmt(ring, x)
    trace = []
    owner = start.find_successor(kid, trace)
    print(f"\nLookup de la clé '{label}' (id={f(kid)}) depuis le nœud {f(start.id)}")
    for step, (n, idx, nxt) in enumerate(trace, 1):
        print(f"  {step}. nœud {f(n.id)} : clé hors de ]{f(n.id)}, {f(n.successor.id)}] → "
              f"finger[{idx}] (start={f(n.start[idx])}) → nœud {f(nxt.id)}")
    last = trace[-1][2] if trace else start
    print(f"  {len(trace) + 1}. nœud {f(last.id)} : clé ∈ ]{f(last.id)}, "
          f"{f(last.live_successor().id)}] → successeur responsable = {f(owner.id)}")
    print(f"  ⇒ la clé {f(kid)} est gérée par le nœud {f(owner.id)} ('{owner.name}') "
          f"en {len(trace)} saut(s)")
    if kid in owner.keys:
        print(f"  ⇒ valeur trouvée : {owner.keys[kid][1]!r}")
    return owner


# ----------------------------------------------------------------------------
# Menu interactif
# ----------------------------------------------------------------------------
def ask(prompt, default=None):
    try:
        s = input(prompt).strip()
    except EOFError:
        print()
        sys.exit(0)
    return s if s or default is None else default


def ask_int(prompt, default=None, lo=None, hi=None):
    while True:
        s = ask(prompt, None if default is None else str(default))
        try:
            v = int(s)
            if (lo is not None and v < lo) or (hi is not None and v > hi):
                print(f"  valeur attendue dans [{lo}, {hi}]")
                continue
            return v
        except ValueError:
            print("  entier attendu")


def need_ring(ring):
    if ring is None or not ring.nodes:
        print("  ! créez d'abord l'anneau (option 1)")
        return False
    return True


def menu_create():
    m = ask_int("m (nombre de bits des identifiants, 1..160) : ", 4, 1, 160)
    ring = Ring(m)
    s = ask("Pairs initiaux (noms séparés par des espaces, ex: A B C ou #0 #1 #3), "
            "ou un nombre : ")
    names = []
    if s.isdigit():
        for _ in range(int(s)):
            names.append(ring.free_name())
    elif s:
        names = s.split()
    else:
        names = [ring.free_name() for _ in range(3)]
    for nm in names:
        try:
            ring.join(nm)
        except ValueError as e:
            print(f"  ! {nm} ignoré : {e}")
    print(f"Anneau créé avec {len(ring.nodes)} pair(s).")
    show_ring(ring)
    return ring


def menu_join(ring):
    name = ask("Nom du nouveau pair (ou #id) [vide = automatique] : ")
    try:
        if not name:
            name = ring.free_name()
        boot_tok = ask("Pair d'entrée (nom/id) [vide = au hasard] : ")
        boot = ring.resolve(boot_tok) if boot_tok else random.choice(list(ring.nodes.values()))
        if boot is None:
            print("  ! pair d'entrée inconnu")
            return
        n = ring.join(name, boot)
    except ValueError as e:
        print(f"  ! {e}")
        return
    print(f"\nLe pair {n.id} ('{n.name}') a rejoint l'anneau via {boot.id}.")
    show_finger_table(n)
    ok, errs = ring.verify()
    print("  vérification globale :", "✔ tables cohérentes" if ok else f"✘ {errs[:3]}")


def menu_lookup(ring):
    tok = ask("Nœud de départ (nom/id) [vide = au hasard] : ")
    start = ring.resolve(tok) if tok else random.choice(list(ring.nodes.values()))
    if start is None:
        print("  ! nœud inconnu")
        return
    label = ask("Clé k (texte, ou #id pour un identifiant direct) : ")
    if not label:
        return
    try:
        lookup(ring, start, label)
    except ValueError as e:
        print(f"  ! {e}")


def menu_leave(ring):
    tok = ask("Pair qui quitte le réseau (nom/id) : ")
    n = ring.resolve(tok)
    if n is None:
        print("  ! pair inconnu")
        return
    ring.leave(n)
    print(f"Le pair {n.id} ('{n.name}') a quitté le réseau ; clés transférées à son "
          f"successeur et finger tables mises à jour.")
    ok, errs = ring.verify()
    print("  vérification globale :", "✔ tables cohérentes" if ok else f"✘ {errs[:3]}")
    if ring.nodes:
        show_ring(ring, with_fingers=False)


def menu_concurrent(ring):
    print("  a) p arrivées simultanées   b) p départs simultanés   "
          "c) p arrivées et q départs simultanés")
    ch = ask("  choix : ").lower()
    pj = pl = 0
    if ch == "a":
        pj = ask_int("  p (arrivées) : ", 3, 1)
    elif ch == "b":
        pl = ask_int("  p (départs) : ", 2, 1, len(ring.nodes) - 1 or 1)
    elif ch == "c":
        pj = ask_int("  p (arrivées) : ", 2, 0)
        pl = ask_int("  q (départs) : ", 2, 0, len(ring.nodes) - 1 or 0)
    else:
        return
    if pl >= len(ring.nodes):
        print("  ! il doit rester au moins un pair")
        return
    names = []
    try:
        for _ in range(pj):
            nm = ring.free_name()
            ring.nodes[ring.make_id(nm)] = None      # réserve l'id le temps de générer
            names.append(nm)
    except ValueError as e:
        print(f"  ! {e}")
    for nm in names:
        del ring.nodes[ring.make_id(nm)]
    leavers = random.sample(list(ring.nodes.values()), pl)
    print(f"  arrivées : {names or '-'} ; départs : {[l.id for l in leavers] or '-'}")
    ring.concurrent_ops(names, leavers)
    ok, errs = ring.verify()
    print("  vérification globale :", "✔ tables cohérentes" if ok else f"✘ {errs[:3]}")
    show_ring(ring)


def menu_insert(ring):
    label = ask("Clé (texte ou #id) : ")
    val = ask("Valeur : ")
    if not label:
        return
    start = random.choice(list(ring.nodes.values()))
    kid, owner = ring.insert(start, label, val)
    print(f"  clé {fmt(ring, kid)} stockée sur le nœud {fmt(ring, owner.id)} ('{owner.name}')")


def main_menu():
    ring = None
    while True:
        print("""
================ Chord DHT ================
 1. Créer l'anneau overlay (m bits, SHA-1) + pairs initiaux
 2. Joindre un pair (affiche sa finger table)
 3. Lookup d'une clé k (via les finger tables)
 4. Un pair quitte le réseau (mise à jour des finger tables)
 5. Afficher l'anneau, les pairs et les finger tables
 6. Arrivée / sortie de p pairs en concurrence
 7. Insérer une donnée (clé/valeur)
 8. Vérifier la cohérence des tables
 0. Quitter""")
        c = ask("Votre choix : ")
        try:
            if c == "1":
                ring = menu_create()
            elif c == "0":
                break
            elif c in "2345678" and len(c) == 1:
                if not need_ring(ring):
                    continue
                {"2": menu_join, "3": menu_lookup, "4": menu_leave,
                 "5": lambda r: show_ring(r), "6": menu_concurrent,
                 "7": menu_insert,
                 "8": lambda r: print("  ✔ cohérent" if r.verify()[0]
                                      else f"  ✘ {r.verify()[1][:5]}")}[c](ring)
            else:
                print("  choix invalide")
        except (ValueError, LookupFailed) as e:
            print(f"  ! erreur : {e}")


# ----------------------------------------------------------------------------
# Démo et auto-tests
# ----------------------------------------------------------------------------
def demo():
    print(">>> Exemple du papier : m=3, nœuds 0, 1, 3, clés 1, 2, 6")
    ring = Ring(3)
    for nm in ("#0", "#1", "#3"):
        ring.join(nm)
    for k in (1, 2, 6):
        ring.insert(ring.nodes[0], f"#{k}", f"valeur-{k}")
    show_ring(ring)
    lookup(ring, ring.nodes[3], "#1")
    print("\n>>> Join du nœud 6")
    n = ring.join("#6")
    show_finger_table(n)
    print("\n>>> Le nœud 3 quitte le réseau")
    ring.leave(ring.nodes[3])
    show_ring(ring)
    print("vérification :", ring.verify())
    print("\n>>> Concurrence : m=6, 8 pairs, puis 6 arrivées + 3 départs simultanés")
    random.seed(1)
    ring = Ring(6)
    for _ in range(8):
        ring.join(ring.free_name())
    names = [ring.free_name() for _ in range(6)]
    leavers = random.sample(list(ring.nodes.values()), 3)
    ring.concurrent_ops(names, leavers)
    print("vérification :", ring.verify())
    show_ring(ring, with_fingers=False)


def selftest():
    random.seed(7)
    for m in (3, 4, 6, 8, 12, 20, 160):
        ring = Ring(m)
        labels = []
        for step in range(60):
            op = random.random()
            if op < 0.5 or len(ring.nodes) < 2:
                try:
                    ring.join(ring.free_name(), random.choice(list(ring.nodes.values())) if ring.nodes else None)
                except ValueError:
                    pass
            else:
                ring.leave(random.choice(list(ring.nodes.values())))
            if random.random() < 0.4 and ring.nodes:
                lb = f"k{step}"
                ring.insert(random.choice(list(ring.nodes.values())), lb, step)
            ok, errs = ring.verify()
            assert ok, (m, step, errs[:3])
        print(f"séquentiel m={m:>3} : OK ({len(ring.nodes)} pairs)")
    for m in (5, 8, 16):
        for trial in range(15):
            ring = Ring(m)
            for _ in range(random.randint(4, 12)):
                try:
                    ring.join(ring.free_name())
                except ValueError:
                    break
            for i in range(10):
                ring.insert(random.choice(list(ring.nodes.values())), f"d{i}", i)
            pj = random.randint(0, 6)
            pl = random.randint(0, max(0, len(ring.nodes) - 1))
            names = []
            for _ in range(pj):
                try:
                    nm = ring.free_name()
                except ValueError:
                    break
                ring.nodes[ring.make_id(nm)] = None
                names.append(nm)
            for nm in names:
                del ring.nodes[ring.make_id(nm)]
            leavers = random.sample(list(ring.nodes.values()), pl)
            ok = ring.concurrent_ops(names, leavers, verbose=False)
            good, errs = ring.verify()
            assert ok and good, (m, trial, errs[:3])
            total_keys = sum(len(n.keys) for n in ring.nodes.values())
            assert total_keys == 10, (m, trial, total_keys)
        print(f"concurrent m={m:>3} : OK (15 essais)")
    print("Tous les tests passent.")


if __name__ == "__main__":
    if "--demo" in sys.argv:
        demo()
    elif "--selftest" in sys.argv:
        selftest()
    else:
        main_menu()
