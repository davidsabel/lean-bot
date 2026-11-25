import Lean
/-
  Mission 1: Rekursion und erste Beweise
  ======================================
  Natürliche Zahlen sind in Lean so gebaut: Jede Zahl ist entweder
  `0` oder `n + 1` (der Nachfolger von n). Funktionen auf Nat
  definiert man deshalb mit zwei Fällen. Das ist Rekursion.
-/

-- summe n = 0 + 1 + 2 + ... + n
def summe : Nat → Nat
  | 0     => 0
  | n + 1 => summe n + (n + 1)

#eval summe 4      -- 10
#eval summe 100    -- 5050 (das hat schon der kleine Gauß gewusst)

-- Tests sind kleine Beweise, Lean rechnet sie aus:
theorem beispiel_1_1 : summe 4 = 10 := rfl
theorem beispiel_1_2 : summe 100 = 5050 := by decide

/-
  DEINE AUFGABE 1: Fakultät
  fak 0 = 1, fak (n+1) = (n+1) * fak n
-/
def fak : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * fak n

#eval fak 5        -- soll 120 ergeben
theorem beispiel_1_3 : fak 5 = 120 := rfl

/-
  DEINE AUFGABE 2: Anzahl der Teilmengen
  Eine Menge mit n Elementen hat 2^n Teilmengen.
  Programmiere `teilmengen n` rekursiv OHNE ^ zu benutzen.
  Tipp: Ein neues Element verdoppelt die Anzahl.
-/
def teilmengen : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * teilmengen n

theorem beispiel_1_4 : teilmengen 10 = 1024 := rfl

/-
  Ausblick: Tests prüfen EINZELNE Werte. Ein Beweis sagt etwas über
  ALLE n. Das kommt in Mission 4 (Induktion). Spoiler: Induktion ist
  einfach eine rekursive Funktion, die Beweise zurückgibt.
-/

/-
  ═════════════════════════════════════════════════════════════
  PRÜFSTATION der Discrete Droid Academy. Bitte nicht ändern!
  Klicke auf die letzte Zeile (#mission). Rechts steht dann,
  ob die Mission geschafft ist, und dein Code für ILIAS.
  ═════════════════════════════════════════════════════════════
-/
open Lean Elab Command in
elab "#mission " n:num " prüft " ids:ident* : command => do
  let mut offen : Array String := #[]
  for id in ids do
    let name := id.getId
    if (← getEnv).find? name |>.isNone then
      offen := offen.push s!"{name} (fehlt)"
    else
      let ax ← Lean.collectAxioms name
      if ax.contains ``sorryAx then offen := offen.push s!"{name}"
  if offen.isEmpty then
    let s := s!"DDA-2026|{n.getNat}|" ++ ", ".intercalate (ids.toList.map (·.getId.toString))
    let mut h : UInt64 := 14695981039346656037
    for b in s.toUTF8 do h := (h ^^^ b.toUInt64) * 1099511628211
    let abc := "ACEFHJKLMNPRTUVWXY3479".toList
    let mut code := ""
    for i in [0:5] do code := code.push (abc[((h >>> (UInt64.ofNat (i*11))) % 22).toNat]!)
    logInfo m!"✅ Mission {n.getNat} geschafft!\nDein Code für ILIAS: LEMMA-{code}"
  else
    logWarning m!"⏳ Mission {n.getNat} ist noch nicht fertig.\nNoch offen: {", ".intercalate offen.toList}"

-- In der Musterlösung gibt es keinen Code. Den bekommst du nur mit deiner eigenen Lösung.
