import Lean
/-
  Mission 0: Hallo Lean!
  ======================
  Lean ist eine Programmiersprache. Rechts im Fenster siehst du,
  was Lean zu jeder Zeile sagt. Klicke auf eine Zeile mit #eval.
-/

-- Rechnen
#eval 2 + 3 * 4
#eval "Discrete " ++ "Droid " ++ "Academy"

-- Eine eigene Funktion: ein Droide verdoppelt seine Energie
def verdopple (n : Nat) : Nat := 2 * n

#eval verdopple 21

-- Funktionen mit zwei Argumenten
def energie (kerne : Nat) (proKern : Nat) : Nat := kerne * proKern

#eval energie 5 12

-- Fallunterscheidung
def ampel (n : Nat) : String :=
  if n < 30 then "rot" else if n < 70 then "gelb" else "grün"

#eval ampel 42

/-
  DEINE AUFGABE
  -------------
  1. Ändere die Zahl in `#eval verdopple 21` und beobachte das Ergebnis.
  2. Schreibe eine Funktion `quadrat`, die n * n berechnet,
     und teste sie mit #eval.
-/

def quadrat (n : Nat) : Nat := n * n

#eval quadrat 7   -- soll 49 ergeben

/-
  Und jetzt das Besondere an Lean: Wir können nicht nur testen,
  sondern BEWEISEN. Die folgende Zeile ist ein Beweis, dass
  verdopple 21 = 42 ist. `rfl` heißt: "einfach ausrechnen, dann sieht man es".
-/
theorem pruefung_verdopple : verdopple 21 = 42 := rfl

-- Wenn du `quadrat` richtig programmiert hast, wird auch dieser Beweis grün:
theorem pruefung_quadrat : quadrat 0 = 0 ∧ quadrat 3 = 9 ∧ quadrat 7 = 49 := ⟨rfl, rfl, rfl⟩

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
