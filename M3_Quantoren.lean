import Lean
/-
  Mission 3: Quantoren
  ====================
  Hängst du fest? Hier ist dieselbe Mission mit Tipps (Strg+Klick):
  https://live.lean-lang.org/#url=https%3A%2F%2Fgist.githubusercontent.com%2Fdavidsabel%2F12dc468ede87291e5ad712797f23ed1a%2Fraw%2FM3_Quantoren_Tipps.lean

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
theorem aufgabe_3_1 : ∃ n : Nat, n + n = 26 := sorry

-- Eine eigene Aussageform: n ist gerade, wenn n = 2 * k für ein k.
def gerade (n : Nat) : Prop := ∃ k, n = 2 * k

-- 👀 VORMACHEN
theorem beispiel_gerade : gerade 10 := ⟨5, rfl⟩

-- ✍️ NACHMACHEN (Aufgabe 3.2): 42 ist gerade.
theorem aufgabe_3_2 : gerade 42 := sorry

/- ─────────────────────────────────────────────────────────────
  Schritt 2: Für alle ... (eine Funktion)
──────────────────────────────────────────────────────────────── -/

-- 👀 VORMACHEN: 4n ist immer gerade. Für jedes n ist 2n der Zeuge, omega rechnet nach.
theorem beispiel_alle : ∀ n : Nat, gerade (4 * n) :=
  fun n => ⟨2 * n, by omega⟩

-- ✍️ NACHMACHEN (Aufgabe 3.3): 2n ist immer gerade.
theorem aufgabe_3_3 : ∀ n : Nat, gerade (2 * n) :=
  sorry

-- 👀 VORMACHEN: Ist n gerade, dann auch n + 4. Mit Taktiken:
theorem beispiel_plus4 : ∀ n : Nat, gerade n → gerade (n + 4) := by
  intro n h
  obtain ⟨k, hk⟩ := h        -- h auspacken: hk : n = 2 * k
  exact ⟨k + 2, by omega⟩    -- n + 4 = 2 * (k + 2)

-- ✍️ NACHMACHEN (Aufgabe 3.4): Ist n gerade, dann auch n + 2.
theorem aufgabe_3_4 : ∀ n : Nat, gerade n → gerade (n + 2) := by
  sorry

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
  sorry

-- 🚀 SELBSTMACHEN (Aufgabe 3.6): Widerlege "Jede natürliche Zahl ist gerade".
theorem aufgabe_3_6 : ¬ (∀ n : Nat, gerade n) := by
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


#mission 3 prüft aufgabe_3_1 aufgabe_3_2 aufgabe_3_3 aufgabe_3_4 aufgabe_3_5 aufgabe_3_6
