import Lean
/-
  Mission 1: Rekursion und erste Beweise
  ======================================
  Hängst du fest? Unter jeder Aufgabe steht eine Zeile wie  -- #tipp 1 1
  Lösche die zwei Striche am Anfang: Rechts erscheint Tipp 1.
  Mit  #tipp 1 1 2  kommt Tipp 2, mit  #tipp 1 1 3  die Lösung dieser Aufgabe.

  Natürliche Zahlen sind in Lean so gebaut: Jede Zahl ist entweder
  `0` oder `n + 1` (der Nachfolger von n). Funktionen auf Nat
  definiert man deshalb mit zwei Fällen:
    | 0     => ...   was kommt für 0 heraus?
    | n + 1 => ...   wie kommt man von n zu n + 1?   (hier darf man die Funktion für n benutzen)
  Das ist Rekursion.
-/

/- ⚙️ Werkzeuge der Discrete Droid Academy: Tipps und Prüfstation (bitte nicht ändern).
   Weiter unten geht es los! -/
def tippHex (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
def tippText (hex : String) : String := Id.run do
  let k := "DDA-2026".toUTF8
  let cs := hex.toList.toArray
  let mut b : ByteArray := .empty
  for i in [0:cs.size / 2] do
    b := b.push ((tippHex cs[2*i]! * 16 + tippHex cs[2*i+1]!) ^^^ (k.get! (i % k.size)).toNat).toUInt8
  return (String.fromUTF8? b).getD "?"
open Lean Elab Command in
elab "#tipp " m:num a:num s:(num)? : command => do
  let stufe := (s.map (·.getNat)).getD 1
  let tabelle : List (Nat × Nat × Nat × String) := [
    (1, 1, 1, "0225325912475b53642624441243475b29216f0d65514116332d33491252575f2964124e5a425b42306437425c105c163e316143121b1207642020574757574c87e02941460f"),
    (1, 1, 2, "1730205946101a58646f611c1b1059592929350d1a5e121d6475680d18101a58646f611c1b1056573e317b0d41455f5b2115344c5642534221642f0d19101a58646f611c1b1018166c2a610612011b"),
    (1, 1, 3, "2021270d41455f5b2115344c5642534221647b0d7c514616a6c2d30d7c51463c64643d0d0210121664647c131200381664386143121b120764797f0d41455f5b2115344c5642534221642f0d19101a58646f611c1b1018166c2a610612011b"),
    (1, 2, 1, "02252d411200081613212d4e5a55126c252c2d0df1945c522136350d57595c1614362e49475b46162a2d2245460f127025282d0d5c101916757e6168404357423e2161445c1041432929240d565141166f64255840535a166e6a"),
    (1, 2, 2, "3864710d0f0e120764312f49124c1258646f611c120d0c1622252a0d5c1018166c2a610612011b"),
    (1, 2, 3, "2021270d545159167e640f4c4610d0b0d6640f4c463a12163864710d12101216797a611c3810124a642a61061201120b7a64274c59105c166e646943121b12076d"),
    (1, 3, 1, "002d240d5e55574421640c485c5757162c25350d55555c57316424445c551262212d2d40575e5553646c3244515812452128235e46191c16112a250d57595c162a2134484110775a212924434610445336202e5d42555e426420284812715c4c252c2d17127a57522164204146551262212d2d40575e55536423284f46105745642128435f515e162b2c2f4812455c52642128435f515e16292d350d56555f162a2134485c10775a21292443461e"),
    (1, 3, 2, "3864710d0f0e120764312f49124c1258646f611c120d0c1676646b0d46555b5a29212f4a575e1258"),
    (1, 3, 3, "2021270d46555b5a29212f4a575e120c640a205912d2b4a4640a20593810124a6474610d1210120b7a64702712104e162a646a0d03100f08647661071244575f2829244355555c162a")
  ]
  let nr := s!"{m.getNat}.{a.getNat}"
  match tabelle.find? (fun (x, y, z, _) => x == m.getNat && y == a.getNat && z == stufe) with
  | some (_, _, z, hex) =>
    if z == 3 then
      logInfo m!"🔑 Lösung zu Aufgabe {nr}:\n\n{tippText hex}"
    else
      logInfo m!"💡 Aufgabe {nr}, Tipp {z}: {tippText hex}\n\nNoch ein Schritt weiter: #tipp {m.getNat} {a.getNat} {z + 1}"
  | none => logWarning m!"Zu Aufgabe {nr} gibt es keinen Tipp {stufe}. Probiere z.B. #tipp {m.getNat} 1"
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

/- ─────────────────────────────────────────────────────────────
  Schritt 1: Summen
──────────────────────────────────────────────────────────────── -/

-- Beispiel: summe n = 0 + 1 + 2 + ... + n
def summe : Nat → Nat
  | 0     => 0
  | n + 1 => summe n + (n + 1)

#eval summe 4      -- 10
#eval summe 100    -- 5050 (das hat schon der kleine Gauß gewusst)

-- Tests sind kleine Beweise, Lean rechnet sie aus:
theorem test_summe : summe 4 = 10 := rfl

-- ✏️ Aufgabe 1.1: Summe der Quadrate 0 + 1 + 4 + 9 + ... + n*n
def summeQuadrate : Nat → Nat
  | 0     => 0
  | n + 1 => sorry
-- #tipp 1 1

#eval summeQuadrate 3   -- soll 14 ergeben (0 + 1 + 4 + 9)
theorem test_summeQuadrate : summeQuadrate 3 = 14 := rfl

/- ─────────────────────────────────────────────────────────────
  Schritt 2: Produkte
──────────────────────────────────────────────────────────────── -/

-- ✏️ Aufgabe 1.2: Fakultät, fak n = 1 * 2 * ... * n
-- Wie `summe`, nur wird multipliziert statt addiert.
-- Achtung beim Startwert: Ein leeres Produkt ist 1, nicht 0.
def fak : Nat → Nat
  | 0     => sorry
  | n + 1 => sorry
-- #tipp 1 2

#eval fak 5        -- soll 120 ergeben
theorem test_fak : fak 5 = 120 := rfl

/- ─────────────────────────────────────────────────────────────
  Schritt 3: selbst eine Rekursion finden
──────────────────────────────────────────────────────────────── -/

-- ✏️ Aufgabe 1.3: Anzahl der Teilmengen
-- Eine Menge mit n Elementen hat 2^n Teilmengen.
-- Programmiere `teilmengen n` rekursiv OHNE ^ zu benutzen.
def teilmengen : Nat → Nat
  | 0     => sorry
  | n + 1 => sorry
-- #tipp 1 3

#eval teilmengen 3      -- soll 8 ergeben
theorem test_teilmengen : teilmengen 10 = 1024 := rfl

/-
  Ausblick: Tests prüfen EINZELNE Werte. Ein Beweis sagt etwas über
  ALLE n. Das kommt in Mission 4 (Induktion). Spoiler: Induktion ist
  einfach eine rekursive Funktion, die Beweise zurückgibt.
-/

/- ═══ PRÜFSTATION ═══ Klicke auf die nächste Zeile. Rechts steht dann, ob die Mission
   geschafft ist, und dein Code für ILIAS. Bitte die Zeile nicht ändern. -/
#mission 1 prüft test_summeQuadrate test_fak test_teilmengen
