import Lean
/-
  Mission 2: Beweise sind Programme
  =================================
  In Lean ist eine Aussage ein TYP und ein Beweis ist ein WERT dieses Typs.
  Eine Aussage zu beweisen heißt also: ein Programm schreiben, das den
  passenden Typ hat. Lean prüft den Typ, genau wie ein Compiler.

  Übersetzungstabelle (Logik  ↔  Programmieren):
    A → B      Funktion, die aus einem Beweis von A einen Beweis von B macht
    A ∧ B      Paar ⟨a, b⟩ aus einem Beweis von A und einem von B
    A ∨ B      entweder links (Or.inl a) oder rechts (Or.inr b)
    ¬A         Funktion A → False ("aus A folgt Unsinn")
-/

-- A → A: Die Identitätsfunktion ist ein Beweis!
theorem beispiel_2_1 (A : Prop) : A → A :=
  fun a => a

-- A ∧ B → B ∧ A: Paar auspacken und vertauscht wieder einpacken
theorem beispiel_2_2 (A B : Prop) : A ∧ B → B ∧ A :=
  fun ⟨a, b⟩ => ⟨b, a⟩

-- A ∨ B → B ∨ A: Fallunterscheidung mit match
theorem beispiel_2_3 (A B : Prop) : A ∨ B → B ∨ A :=
  fun h => match h with
    | Or.inl a => Or.inr a
    | Or.inr b => Or.inl b

/-
  DEINE AUFGABEN (ersetze jedes `sorry` durch ein Programm)
-/

-- Aufgabe 1: Aus A folgt (B → A). Tipp: eine Funktion, die ihr zweites Argument ignoriert.
theorem beispiel_2_4 (A B : Prop) : A → (B → A) :=
  sorry

-- Aufgabe 2: Kettenschluss. Erkennst du die Komposition von Funktionen?
theorem beispiel_2_5 (A B C : Prop) : (A → B) → (B → C) → (A → C) :=
  sorry

-- Aufgabe 3: A → ¬¬A. Denke daran: ¬¬A ist (A → False) → False.
theorem beispiel_2_6 (A : Prop) : A → ¬¬A :=
  sorry

/-
  Taktik-Modus
  ------------
  Statt das Programm direkt hinzuschreiben, kann man es Schritt für Schritt
  bauen lassen. Nach `by` stehen Befehle (Taktiken). Rechts siehst du jeweils,
  was noch zu zeigen ist (das "Ziel").
    intro h        nimm die Voraussetzung h an (baut fun h => ...)
    exact t        das Ziel ist genau t
    constructor    Ziel A ∧ B in zwei Ziele A und B zerlegen
    cases h with   Fallunterscheidung über h : A ∨ B
    left / right   Ziel A ∨ B: zeige A bzw. B
-/
theorem beispiel_2_7 (A B : Prop) : A ∧ B → B ∧ A := by
  intro h
  constructor
  · exact h.2
  · exact h.1

-- Aufgabe 4 (De Morgan, Distributivgesetz): mit Taktiken
theorem beispiel_2_8 (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
  sorry

-- Aufgabe 5: De Morgan, eine Richtung
theorem beispiel_2_9 (A B : Prop) : ¬(A ∨ B) → ¬A ∧ ¬B := by
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

#mission 2 prüft beispiel_2_3 beispiel_2_4 beispiel_2_5 beispiel_2_6 beispiel_2_8 beispiel_2_9
