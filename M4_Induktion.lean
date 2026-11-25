import Lean
/-
  Mission 4: Induktion ist Rekursion
  ==================================
  Hängst du fest? Hier ist dieselbe Mission mit Tipps (Strg+Klick):
  https://live.lean-lang.org/#url=https%3A%2F%2Fgist.githubusercontent.com%2Fdavidsabel%2F12dc468ede87291e5ad712797f23ed1a%2Fraw%2FM4_Induktion_Tipps.lean

  Tests prüfen einzelne Werte. Mit Induktion beweisen wir Aussagen für ALLE n.

  Ein Beweis durch Induktion ist eine REKURSIVE FUNKTION, die Beweise
  zurückgibt: Für 0 liefert sie den Induktionsanfang, für n + 1 benutzt sie
  den Beweis für n (das ist die Induktionsvoraussetzung!).
-/

/- ─────────────────────────────────────────────────────────────
  Schritt 1: Induktion über Zahlen
──────────────────────────────────────────────────────────────── -/

-- Aus Mission 1 kennst du:
def summe : Nat → Nat
  | 0     => 0
  | n + 1 => summe n + (n + 1)

-- Beispiel: die Gaußsche Formel für ALLE n, mit der Taktik `induction`.
-- Klicke auf die Zeilen und schau rechts, was jeweils zu zeigen ist.
theorem gauss (n : Nat) : 2 * summe n = n * (n + 1) := by
  induction n with
  | zero => rfl                 -- Induktionsanfang: einfach ausrechnen
  | succ n iv =>                -- iv ist die Induktionsvoraussetzung für n
      simp only [summe]         -- summe (n + 1) durch seine Definition ersetzen
      grind                     -- den Rest (Rechnen mit iv) erledigt grind

-- ✏️ Aufgabe 4.1: die Summe der ersten n ungeraden Zahlen 1 + 3 + 5 + ...
def ungerade : Nat → Nat
  | 0     => 0
  | n + 1 => ungerade n + (2 * n + 1)

#eval ungerade 5     -- 25. Vermutung?

theorem ungerade_formel (n : Nat) : ungerade n = n * n := by
  sorry

-- ✏️ Aufgabe 4.2: `teilmengen` aus Mission 1. Zeige teilmengen n = 2 ^ n.
def teilmengen : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * teilmengen n

theorem teilmengen_formel (n : Nat) : teilmengen n = 2 ^ n := by
  sorry

/- ─────────────────────────────────────────────────────────────
  Schritt 2: Induktion über Listen
──────────────────────────────────────────────────────────────── -/
/-
  Listen sind auch rekursiv gebaut: Eine Liste ist entweder leer `[]`
  oder `x :: xs` (ein Element x vor einer Liste xs).
  Darum funktioniert Induktion auch für Listen, mit den Fällen `nil` und `cons`.
-/

-- Jedes Element um 1 erhöhen
def plusEins : List Nat → List Nat
  | []      => []
  | x :: xs => (x + 1) :: plusEins xs

#eval plusEins [1, 2, 3]   -- [2, 3, 4]

-- Beispiel: plusEins ändert die Länge der Liste nicht.
theorem plusEins_laenge (xs : List Nat) : (plusEins xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs iv =>
      simp only [plusEins, List.length_cons, iv]

-- Jedes Element verdoppeln
def verdopple : List Nat → List Nat
  | []      => []
  | x :: xs => (2 * x) :: verdopple xs

#eval verdopple [1, 2, 3]   -- [2, 4, 6]

-- ✏️ Aufgabe 4.3: verdopple ändert die Länge der Liste nicht.
theorem laenge_bleibt (xs : List Nat) : (verdopple xs).length = xs.length := by
  sorry

-- ✏️ Aufgabe 4.4: Die Summe der verdoppelten Liste ist doppelt so groß.
theorem summe_verdoppelt (xs : List Nat) : (verdopple xs).sum = 2 * xs.sum := by
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


#mission 4 prüft ungerade_formel teilmengen_formel laenge_bleibt summe_verdoppelt
