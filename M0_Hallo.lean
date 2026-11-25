import Lean
/-
  Mission 0: Hallo Lean!
  ======================
  Hängst du fest? Tipps Schritt für Schritt (Strg+Klick):
  https://github.com/davidsabel/lean-bot/blob/main/hilfen/M0.md

  Lean ist eine Programmiersprache. Rechts im Fenster siehst du,
  was Lean zu jeder Zeile sagt. Klicke auf eine Zeile mit #eval.

  So ist jede Mission aufgebaut:
    👀 VORMACHEN    Ein fertiges Beispiel. Lies es und klicke es an.
    ✍️ NACHMACHEN   Fast dasselbe noch einmal. Ersetze `sorry` nach dem Vorbild.
    🚀 SELBSTMACHEN Ein kleiner Schritt weiter, diesmal ohne Vorlage.
  Ersetze jedes `sorry`. Lean zeigt dir sofort, ob es passt.
-/

-- Rechnen
#eval 2 + 3 * 4
#eval "Discrete " ++ "Droid " ++ "Academy"

/- ─────────────────────────────────────────────────────────────
  Schritt 1: eine eigene Funktion
──────────────────────────────────────────────────────────────── -/

-- 👀 VORMACHEN: Ein Droide verdoppelt seine Energie.
def verdopple (n : Nat) : Nat := 2 * n

#eval verdopple 21     -- 42

-- Das Besondere an Lean: Wir können nicht nur testen, sondern BEWEISEN.
-- `rfl` heißt: "einfach ausrechnen, dann sieht man es".
theorem test_verdopple : verdopple 21 = 42 := rfl

-- ✍️ NACHMACHEN (Aufgabe 0.1): Ein Droide verdreifacht seine Energie.
def verdreifache (n : Nat) : Nat := sorry

#eval verdreifache 5   -- soll 15 ergeben
theorem test_verdreifache : verdreifache 5 = 15 := rfl

/- ─────────────────────────────────────────────────────────────
  Schritt 2: Funktionen mit zwei Argumenten
──────────────────────────────────────────────────────────────── -/

-- 👀 VORMACHEN
def energie (kerne : Nat) (proKern : Nat) : Nat := kerne * proKern

#eval energie 5 12     -- 60

-- ✍️ NACHMACHEN (Aufgabe 0.2): die Fläche eines Rechtecks
def flaeche (breite : Nat) (hoehe : Nat) : Nat := sorry

theorem test_flaeche : flaeche 3 4 = 12 := rfl

-- 🚀 SELBSTMACHEN (Aufgabe 0.3): Diesmal schreibst du die ganze Zeile nach `:=` selbst.
-- `quadrat n` soll n * n berechnen.
def quadrat (n : Nat) : Nat := sorry

#eval quadrat 7        -- soll 49 ergeben
theorem test_quadrat : quadrat 0 = 0 ∧ quadrat 3 = 9 ∧ quadrat 7 = 49 := ⟨rfl, rfl, rfl⟩

/- ─────────────────────────────────────────────────────────────
  Schritt 3: Fallunterscheidung
──────────────────────────────────────────────────────────────── -/

-- 👀 VORMACHEN: Ladestand als Ampel
def ampel (n : Nat) : String :=
  if n < 30 then "rot" else if n < 70 then "gelb" else "grün"

#eval ampel 42         -- "gelb"

-- ✍️ NACHMACHEN (Aufgabe 0.4): Ab 50 Punkten ist ein Test bestanden.
def bewertung (punkte : Nat) : String :=
  sorry

theorem test_bewertung : bewertung 49 = "nicht bestanden" ∧ bewertung 50 = "bestanden" := ⟨rfl, rfl⟩


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


#mission 0 prüft test_verdreifache test_flaeche test_quadrat test_bewertung
