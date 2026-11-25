import Lean
/-
  Mission 4: Induktion ist Rekursion
  ==================================
  Aus Mission 1 kennst du:
-/
def summe : Nat → Nat
  | 0     => 0
  | n + 1 => summe n + (n + 1)

/-
  Tests prüfen einzelne Werte. Jetzt beweisen wir die Gaußsche Formel
  für ALLE n:   2 * summe n = n * (n + 1)

  Ein Beweis durch Induktion ist eine REKURSIVE FUNKTION, die Beweise
  zurückgibt: Für 0 liefert sie den Induktionsanfang, für n + 1 ruft sie
  sich selbst für n auf (das ist die Induktionsvoraussetzung!).
-/
theorem gauss : ∀ n : Nat, 2 * summe n = n * (n + 1)
  | 0     => rfl                       -- Induktionsanfang: einfach ausrechnen
  | n + 1 => by
      have iv := gauss n               -- rekursiver Aufruf = Induktionsvoraussetzung
      simp only [summe]                -- summe (n+1) = summe n + (n+1) einsetzen
      grind                            -- Rechnen mit +, * erledigt grind

/-
  Dasselbe mit der Taktik `induction`, so wie man es auf Papier aufschreibt:
-/
theorem gauss' (n : Nat) : 2 * summe n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n iv =>
      simp only [summe]
      grind

/-
  DEINE AUFGABEN
-/

-- Aufgabe 1: die Summe der ersten n ungeraden Zahlen 1 + 3 + 5 + ...
def ungerade : Nat → Nat
  | 0     => 0
  | n + 1 => ungerade n + (2 * n + 1)

#eval ungerade 5     -- 25. Vermutung?

theorem ungerade_formel (n : Nat) : ungerade n = n * n := by
  sorry

-- Aufgabe 2: teilmengen aus Mission 1. Zeige teilmengen n = 2 ^ n.
def teilmengen : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * teilmengen n

theorem teilmengen_formel (n : Nat) : teilmengen n = 2 ^ n := by
  sorry

-- Aufgabe 3: Eine Programmeigenschaft. `verdopple` läuft rekursiv über eine Liste.
def verdopple : List Nat → List Nat
  | []      => []
  | x :: xs => (2 * x) :: verdopple xs

#eval verdopple [1, 2, 3]   -- [2, 4, 6]

-- Zeige: verdopple ändert die Länge der Liste nicht.
theorem laenge_bleibt (xs : List Nat) : (verdopple xs).length = xs.length := by
  sorry

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

#mission 4 prüft ungerade_formel teilmengen_formel laenge_bleibt
