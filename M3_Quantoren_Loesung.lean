import Lean
/-
  Musterlösung zu Mission 3: Quantoren
  ====================
  Hängst du fest? Tipps Schritt für Schritt (Strg+Klick):
  https://github.com/davidsabel/lean-bot/blob/main/hilfen/M3.md

  ∃ x, P x    ist ein Paar ⟨x, Beweis⟩: ein Zeuge x und der Beweis, dass P x gilt.
  ∀ x, P x    ist eine Funktion: Sie bekommt ein x und liefert einen Beweis von P x.

  Zwei hilfreiche Taktiken:
    decide   rechnet endliche Fragen mit konkreten Zahlen aus
    omega    löst lineare Gleichungen und Ungleichungen über Nat automatisch
-/

/- ─────────────────────────────────────────────────────────────
  Schritt 1: Es gibt ... (Zeuge angeben)
──────────────────────────────────────────────────────────────── -/

-- 👀 VORMACHEN: Zeuge 7, den Rest rechnet Lean aus.
theorem beispiel_existiert : ∃ n : Nat, n * n = 49 := ⟨7, rfl⟩

-- ✍️ NACHMACHEN (Aufgabe 3.1): Es gibt ein n mit n + n = 26.
theorem aufgabe_3_1 : ∃ n : Nat, n + n = 26 := ⟨13, rfl⟩

-- Eine eigene Aussageform: n ist gerade, wenn n = 2 * k für ein k.
def gerade (n : Nat) : Prop := ∃ k, n = 2 * k

-- 👀 VORMACHEN
theorem beispiel_gerade : gerade 10 := ⟨5, rfl⟩

-- ✍️ NACHMACHEN (Aufgabe 3.2): 42 ist gerade.
theorem aufgabe_3_2 : gerade 42 := ⟨21, rfl⟩

/- ─────────────────────────────────────────────────────────────
  Schritt 2: Für alle ... (eine Funktion)
──────────────────────────────────────────────────────────────── -/

-- 👀 VORMACHEN: 4n ist immer gerade. Für jedes n ist 2n der Zeuge, omega rechnet nach.
theorem beispiel_alle : ∀ n : Nat, gerade (4 * n) :=
  fun n => ⟨2 * n, by omega⟩

-- ✍️ NACHMACHEN (Aufgabe 3.3): 2n ist immer gerade.
theorem aufgabe_3_3 : ∀ n : Nat, gerade (2 * n) :=
  fun n => ⟨n, by omega⟩

-- 👀 VORMACHEN: Ist n gerade, dann auch n + 4. Mit Taktiken:
theorem beispiel_plus4 : ∀ n : Nat, gerade n → gerade (n + 4) := by
  intro n h
  obtain ⟨k, hk⟩ := h        -- h auspacken: hk : n = 2 * k
  exact ⟨k + 2, by omega⟩    -- n + 4 = 2 * (k + 2)

-- ✍️ NACHMACHEN (Aufgabe 3.4): Ist n gerade, dann auch n + 2.
theorem aufgabe_3_4 : ∀ n : Nat, gerade n → gerade (n + 2) := by
  intro n h
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by omega⟩

/- ─────────────────────────────────────────────────────────────
  Schritt 3: Gegenbeispiele
──────────────────────────────────────────────────────────────── -/
/-
  Beispiele sind kein Beweis! Für n = 0, 1, ..., 39 ist n*n + n + 41 eine Primzahl,
  aber nicht für alle n. Einen ∀-Satz widerlegt man durch EIN Gegenbeispiel.
-/

-- 👀 VORMACHEN: Widerlege "Jede natürliche Zahl ist kleiner als 10".
theorem beispiel_gegen : ¬ (∀ n : Nat, n < 10) := by
  intro h            -- angenommen, es gilt für alle n ...
  have h10 := h 10   -- ... dann auch für 10: h10 : 10 < 10
  omega              -- Widerspruch

-- ✍️ NACHMACHEN (Aufgabe 3.5): Widerlege "Jede natürliche Zahl ist kleiner als 100".
theorem aufgabe_3_5 : ¬ (∀ n : Nat, n < 100) := by
  intro h
  have h100 := h 100
  omega

-- 🚀 SELBSTMACHEN (Aufgabe 3.6): Widerlege "Jede natürliche Zahl ist gerade".
theorem aufgabe_3_6 : ¬ (∀ n : Nat, gerade n) := by
  intro h
  obtain ⟨k, hk⟩ := h 1
  omega


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


-- In der Musterlösung gibt es keinen Code. Den bekommst du nur mit deiner eigenen Lösung.
