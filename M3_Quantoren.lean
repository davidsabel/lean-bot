import Lean
/-
  Mission 3: Quantoren
  ====================
  ∀ x, P x    ist eine Funktion: Sie bekommt ein x und liefert einen Beweis von P x.
  ∃ x, P x    ist ein Paar ⟨x, Beweis⟩: ein Zeuge x und der Beweis, dass P x gilt.
-/

-- ∃: Zeuge angeben, Lean rechnet den Rest aus
theorem beispiel_3_1 : ∃ n : Nat, n * n = 49 := ⟨7, rfl⟩

-- ∀: eine Funktion über alle n
theorem beispiel_3_2 : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl

-- Eine eigene Aussageform: n ist gerade
def gerade (n : Nat) : Prop := ∃ k, n = 2 * k

theorem beispiel_3_3 : gerade 10 := ⟨5, rfl⟩

/-
  Die Taktik `omega` löst lineare Gleichungen und Ungleichungen über
  natürlichen Zahlen automatisch. `decide` rechnet endliche Fragen aus.
-/

-- Aufgabe 1: 2n ist immer gerade
theorem beispiel_3_4 : ∀ n : Nat, gerade (2 * n) :=
  sorry

-- Aufgabe 2: Ist n gerade, dann auch n + 2.
-- Tipp: intro n h, dann h auspacken mit `obtain ⟨k, hk⟩ := h`, Zeuge k + 1, Rest mit omega.
theorem beispiel_3_5 : ∀ n : Nat, gerade n → gerade (n + 2) := by
  sorry

/-
  Beispiele sind kein Beweis!
  Für n = 0, 1, ..., 39 ist n*n + n + 41 eine Primzahl. Aber nicht für alle n.
  Einen ∀-Satz widerlegt man durch ein Gegenbeispiel.
  Wir zeigen: Es stimmt NICHT, dass n*n + n + 41 nie durch 41 teilbar ist.
-/
theorem beispiel_3_6 : ¬ (∀ n : Nat, (n * n + n + 41) % 41 ≠ 0) := by
  intro h
  exact h 41 (by decide)

-- Aufgabe 3: Widerlege "Jede natürliche Zahl ist kleiner als 100".
theorem beispiel_3_7 : ¬ (∀ n : Nat, n < 100) := by
  sorry

-- Aufgabe 4: Negation nach innen ziehen. Zeige: Wenn es KEIN n mit P n gibt,
-- dann gilt für alle n: ¬ P n.
theorem beispiel_3_8 (P : Nat → Prop) : ¬ (∃ n, P n) → ∀ n, ¬ P n := by
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

#mission 3 prüft beispiel_3_4 beispiel_3_5 beispiel_3_7 beispiel_3_8
