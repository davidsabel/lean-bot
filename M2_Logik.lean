import Lean
/-
  Mission 2: Beweise sind Programme
  =================================
  Hängst du fest? Tipps Schritt für Schritt (Strg+Klick):
  https://github.com/davidsabel/lean-bot/blob/main/hilfen/M2.md

  In Lean ist eine Aussage ein TYP und ein Beweis ist ein WERT dieses Typs.
  Eine Aussage zu beweisen heißt also: ein Programm schreiben, das den
  passenden Typ hat. Lean prüft den Typ, genau wie ein Compiler.

  Übersetzungstabelle (Logik  ↔  Programmieren):
    A → B      Funktion, die aus einem Beweis von A einen Beweis von B macht
    A ∧ B      Paar ⟨a, b⟩ aus einem Beweis von A und einem von B
    A ∨ B      entweder links (Or.inl a) oder rechts (Or.inr b)
    ¬A         Funktion A → False ("aus A folgt Unsinn")
-/

/- ─────────────────────────────────────────────────────────────
  Schritt 1: Implikation = Funktion
──────────────────────────────────────────────────────────────── -/

-- 👀 VORMACHEN: A → A. Die Identitätsfunktion ist ein Beweis!
theorem beispiel_id (A : Prop) : A → A :=
  fun a => a

-- 👀 VORMACHEN: A → B → B. Eine Funktion mit zwei Argumenten, die das zweite zurückgibt.
-- `_` heißt: Dieses Argument wird nicht gebraucht.
theorem beispiel_zweites (A B : Prop) : A → B → B :=
  fun _ b => b

-- ✍️ NACHMACHEN (Aufgabe 2.1): A → B → A
theorem aufgabe_2_1 (A B : Prop) : A → B → A :=
  sorry

-- 👀 VORMACHEN: Modus ponens. Eine Funktion f : A → B auf a : A anwenden.
theorem beispiel_mp (A B : Prop) : (A → B) → A → B :=
  fun f a => f a

-- ✍️ NACHMACHEN (Aufgabe 2.2): Kettenschluss
theorem aufgabe_2_2 (A B C : Prop) : (A → B) → (B → C) → A → C :=
  sorry

/- ─────────────────────────────────────────────────────────────
  Schritt 2: Und = Paar
──────────────────────────────────────────────────────────────── -/

-- 👀 VORMACHEN: A ∧ B → B ∧ A. Paar auspacken und vertauscht wieder einpacken.
theorem beispiel_und (A B : Prop) : A ∧ B → B ∧ A :=
  fun ⟨a, b⟩ => ⟨b, a⟩

-- ✍️ NACHMACHEN (Aufgabe 2.3): A ∧ B → A
theorem aufgabe_2_3 (A B : Prop) : A ∧ B → A :=
  sorry

-- 🚀 SELBSTMACHEN (Aufgabe 2.4): A → B → A ∧ B
theorem aufgabe_2_4 (A B : Prop) : A → B → A ∧ B :=
  sorry

/- ─────────────────────────────────────────────────────────────
  Schritt 3: Oder = einer von zwei Fällen
──────────────────────────────────────────────────────────────── -/

-- 👀 VORMACHEN: A → A ∨ B. Man wählt die linke Seite.
theorem beispiel_links (A B : Prop) : A → A ∨ B :=
  fun a => Or.inl a

-- ✍️ NACHMACHEN (Aufgabe 2.5): B → A ∨ B
theorem aufgabe_2_5 (A B : Prop) : B → A ∨ B :=
  sorry

-- 👀 VORMACHEN: A ∨ B → B ∨ A. Fallunterscheidung mit match.
theorem beispiel_oder (A B : Prop) : A ∨ B → B ∨ A :=
  fun h => match h with
    | Or.inl a => Or.inr a
    | Or.inr b => Or.inl b

-- 🚀 SELBSTMACHEN (Aufgabe 2.6): A ∨ A → A
theorem aufgabe_2_6 (A : Prop) : A ∨ A → A :=
  sorry

/- ─────────────────────────────────────────────────────────────
  Schritt 4: Nicht = Funktion nach False
──────────────────────────────────────────────────────────────── -/

-- 👀 VORMACHEN: A → ¬A → False. ¬A ist eine Funktion A → False, man wendet sie auf a an.
theorem beispiel_nicht (A : Prop) : A → ¬A → False :=
  fun a na => na a

-- ✍️ NACHMACHEN (Aufgabe 2.7): A → ¬¬A
-- ¬¬A bedeutet ¬A → False. Also ist das wieder eine Funktion mit zwei Argumenten.
theorem aufgabe_2_7 (A : Prop) : A → ¬¬A :=
  sorry

/- ─────────────────────────────────────────────────────────────
  Schritt 5: Taktik-Modus
──────────────────────────────────────────────────────────────── -/
/-
  Statt das Programm direkt hinzuschreiben, kann man es Schritt für Schritt
  bauen lassen. Nach `by` stehen Befehle (Taktiken). Klicke auf die Zeilen:
  Rechts siehst du jeweils, was noch zu zeigen ist (das "Ziel").
    intro h        nimm die Voraussetzung h an (baut fun h => ...)
    exact t        das Ziel ist genau t
    constructor    Ziel A ∧ B in zwei Ziele A und B zerlegen
    cases h with   Fallunterscheidung über h : A ∨ B
    left / right   Ziel A ∨ B: zeige A bzw. B
-/

-- 👀 VORMACHEN: A ∧ B → B ∧ A mit Taktiken
theorem beispiel_taktik_und (A B : Prop) : A ∧ B → B ∧ A := by
  intro h
  constructor
  · exact h.2
  · exact h.1

-- 👀 VORMACHEN: A ∨ B → B ∨ A mit Taktiken
theorem beispiel_taktik_oder (A B : Prop) : A ∨ B → B ∨ A := by
  intro h
  cases h with
  | inl a => right; exact a
  | inr b => left; exact b

-- ✍️ NACHMACHEN (Aufgabe 2.8): Distributivgesetz. Das Gerüst ist schon da.
theorem aufgabe_2_8 (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
  intro ⟨a, h⟩
  cases h with
  | inl b => sorry
  | inr c => sorry

-- 🚀 SELBSTMACHEN (Aufgabe 2.9): De Morgan, eine Richtung
theorem aufgabe_2_9 (A B : Prop) : ¬(A ∨ B) → ¬A ∧ ¬B := by
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
  -- die letzte Zeile darf nicht verändert werden
  let soll : List String := match n.getNat with
    | 0 => ["test_verdreifache", "test_flaeche", "test_quadrat", "test_bewertung"]
    | 1 => ["test_summeQuadrate", "test_fak", "test_teilmengen"]
    | 2 => ["aufgabe_2_1", "aufgabe_2_2", "aufgabe_2_3", "aufgabe_2_4", "aufgabe_2_5", "aufgabe_2_6", "aufgabe_2_7", "aufgabe_2_8", "aufgabe_2_9"]
    | 3 => ["aufgabe_3_1", "aufgabe_3_2", "aufgabe_3_3", "aufgabe_3_4", "aufgabe_3_5", "aufgabe_3_6"]
    | 4 => ["ungerade_formel", "teilmengen_formel", "laenge_bleibt", "summe_verdoppelt"]
    | 5 => ["beispiel_5_3"]
    | _ => []
  if ids.toList.map (·.getId.toString) != soll then
    logWarning m!"⚠️ Die Zeile #mission wurde verändert. Bitte die Datei neu öffnen."
    return
  let mut offen : Array String := #[]
  for id in ids do
    let name := id.getId
    if (← getEnv).find? name |>.isNone then
      offen := offen.push s!"{name} (fehlt)"
    else
      let ax ← Lean.collectAxioms name
      if ax.contains ``sorryAx then offen := offen.push s!"{name}"
  if offen.isEmpty then
    -- feste Codes je Mission (unabhängig davon, wie die Aufgaben heißen)
    let s := "DDA-2026|" ++ (match n.getNat with
      | 0 => "0|pruefung_verdopple, pruefung_quadrat"
      | 1 => "1|beispiel_1_3, beispiel_1_4"
      | 2 => "2|beispiel_2_3, beispiel_2_4, beispiel_2_5, beispiel_2_6, beispiel_2_8, beispiel_2_9"
      | 3 => "3|beispiel_3_4, beispiel_3_5, beispiel_3_7, beispiel_3_8"
      | 4 => "4|ungerade_formel, teilmengen_formel, laenge_bleibt"
      | k => s!"{k}|beispiel_5_3")
    let mut h : UInt64 := 14695981039346656037
    for b in s.toUTF8 do h := (h ^^^ b.toUInt64) * 1099511628211
    let abc := "ACEFHJKLMNPRTUVWXY3479".toList
    let mut code := ""
    for i in [0:5] do code := code.push (abc[((h >>> (UInt64.ofNat (i*11))) % 22).toNat]!)
    logInfo m!"✅ Mission {n.getNat} geschafft!\nDein Code für ILIAS: LEMMA-{code}"
  else
    logWarning m!"⏳ Mission {n.getNat} ist noch nicht fertig.\nNoch offen: {", ".intercalate offen.toList}"


#mission 2 prüft aufgabe_2_1 aufgabe_2_2 aufgabe_2_3 aufgabe_2_4 aufgabe_2_5 aufgabe_2_6 aufgabe_2_7 aufgabe_2_8 aufgabe_2_9
