import Lean
/-
  Mission 4: Induktion ist Rekursion
  ==================================
  Hängst du fest? Unter jeder Aufgabe steht eine Zeile wie  -- #tipp 4 1
  Lösche die zwei Striche am Anfang: Rechts erscheint Tipp 1.
  Mit  #tipp 4 1 2  kommt Tipp 2, mit  #tipp 4 1 3  die Lösung dieser Aufgabe.

  Tests prüfen einzelne Werte. Mit Induktion beweisen wir Aussagen für ALLE n.

  Ein Beweis durch Induktion ist eine REKURSIVE FUNKTION, die Beweise
  zurückgibt: Für 0 liefert sie den Induktionsanfang, für n + 1 benutzt sie
  den Beweis für n (das ist die Induktionsvoraussetzung!).
-/

/- ⚙️ Tipp-Werkzeug (bitte nicht ändern). Weiter unten geht es los! -/
def tippText (hex : List Char) : String := Id.run do
  let k := "DDA-2026".toList.map Char.toNat
  let w (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
  let mut b : ByteArray := .empty
  for i in [0:hex.length / 2] do
    b := b.push ((w hex[2*i]! * 16 + w hex[2*i+1]!) ^^^ k[i % k.length]!).toUInt8
  return (String.fromUTF8? b).getD "?"
open Lean Elab Command in
elab "#tipp " m:num a:num s:(num)? : command => do
  let (x, y, z) := (m.getNat, a.getNat, (s.map (·.getNat)).getD 1)
  let marke := s!"⟦{x} {y} {z}⟧ ".toList
  let zeilen := ((← getFileMap).source.splitOn "\n").map (·.toList.dropWhile (· == ' '))
  match zeilen.find? (marke.isPrefixOf ·) with
  | none => logWarning m!"Zu Aufgabe {x}.{y} gibt es keinen Tipp {z}."
  | some zeile =>
    let text := tippText ((zeile.drop marke.length).filter (·.isAlphanum))
    if z == 3 then logInfo m!"🔑 Lösung zu Aufgabe {x}.{y}:\n\n{text}"
    else logInfo m!"💡 Aufgabe {x}.{y}, Tipp {z}: {text}\n\nNoch ein Schritt weiter: #tipp {x} {y} {z + 1}"

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
-- #tipp 4 1

#eval ungerade 5     -- 25. Vermutung?

theorem ungerade_formel (n : Nat) : ungerade n = n * n := by
  sorry

-- ✏️ Aufgabe 4.2: `teilmengen` aus Mission 1. Zeige teilmengen n = 2 ^ n.
def teilmengen : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * teilmengen n
-- #tipp 4 2

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
-- #tipp 4 3

-- ✏️ Aufgabe 4.4: Die Summe der verdoppelten Liste ist doppelt so groß.
theorem summe_verdoppelt (xs : List Nat) : (verdopple xs).sum = 2 * xs.sum := by
  sorry
-- #tipp 4 4

/- ═══ PRÜFSTATION ═══ Klicke auf die letzte Zeile der Datei (#mission). Rechts steht dann,
   ob die Mission geschafft ist, und dein Code für ILIAS. Bitte hier nichts ändern. -/
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

/- verschlüsselte Tipps
  ⟦4 1 1⟧ 0021330d705545532d37614553441251212a20581254575837212d4f575e12773122234c4710455f2164264c47434118640f2e5d5b554053642d294312455c526434205e415512532d2a2443127e535b212a614c5c1e
  ⟦4 1 2⟧ 0d2a61495742126c212d2d4812435b5b34642e435e49126d6a6a6f70125d474537642b48464a4616312a2648405156536437354c4644124531292c48124346532c212f03
  ⟦4 1 3⟧ 2021270d475e555336252548120a1278253061cfb4a2127825304b0d124c12066464610d120d0c16744e610d4e105c166f64700d0f0e12432a23245f535457162a646a0d1a02121c642a610612011b
  ⟦4 2 1⟧ 132d244957421252213632485e5257160531274f534512412d21614f575912512531325e1c
  ⟦4 2 2⟧ 0d2a61495742126c212d2d4812435b5b34642e435e49126d6a6a6f70124346532c30614757444842643024445e5d575823212f03
  ⟦4 2 3⟧ 2021270d46555b5a29212f4a575e120c640a205912d2b4a4640a20593810124a6474610d1210120b7a64702712104e162a646a0d03100f08647661071244575f2829244355555c162a
  ⟦4 3 1⟧ 03212f4c4710455f216431414743775f2a371e4153555c51216a
  ⟦4 3 2⟧ 0d2a61495742126c212d2d4812435b5b34642e435e49126d6a6a6f70124346532c306147574448426432245f565f42462821615e4651464264342d5841755b58376a
  ⟦4 3 3⟧ 302c244240555f162825244355556d542821284f46101a4e37647b0d7e594142640a20591b1008166c32245f565f42462821615541191c5a212a26595a100f163c376f41575e55422c647b1012524b3c64642843564551422d2b2f0d4a4312412d30292712104e162a2d2d0d0f0e124422284b0d124c12552b2a320d4a104a45642d370d0f0e38166464610d12435b5b34642e435e49126d322133495d40425a216861615b43461828212f4a46586d552b2a32011259446b
  ⟦4 4 1⟧ 0d2a255859445b592a648291505540163c37615a5b55125326212f0312795f1602252d4112535d58376429445e564616082d32591c43475b1b272e4341101a522d21617e475d5f5364322e431248120c7e64395e12594142643c61061263475b2921615b5d5e124e376d6f
  ⟦4 4 2⟧ 02252d4112535d583764390d4a43125f327e615e5b5d42162b2a2d54126b445336202e5d425c571a6408285e461e4143291b22425c436f16312a250d56515c57272c614a40595c5268643644571050532d64264c47434118
  ⟦4 4 3⟧ 302c244240555f1637312c40576f445336202e5d42555e42646c395e120a127a2d37350d7c51461f647e6105445540522b34314157104a456d6a32585f100f1676646b0d4a431c45312961170f10504f4e6461445c544755302d2e4312484116332d35453810124a642a2841120d0c1636222d2712104e16272b2f5e1248124e3764285b120d0c3c6464610d1210415f293461425c5c4b161f32245f565f424628216d0d7e5941426a3734406d535d5837194b0d12101216642333445c54
-/
#mission 4 prüft ungerade_formel teilmengen_formel laenge_bleibt summe_verdoppelt
