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

/- ⚙️ Tipp-Werkzeug (bitte nicht ändern). Weiter unten geht es los! -/
open Lean Elab Command in
elab "#tipp " m:num a:num s:(num)? : command => do
  let marke := s!"⟦{m.getNat} {a.getNat} {(s.map (·.getNat)).getD 1}⟧ "
  match ((← getFileMap).source.splitOn "\n").find? (·.startsWith marke) with
  | some z => logInfo (String.mk ((z.toList.drop marke.length).map fun c => if c == '¶' then '\n' else Char.ofNat (c.toNat - 1)))
  | none => logWarning "Diesen Tipp gibt es nicht."

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
⟦1 1 1⟧ 💢!Bvghbcf!2/2-!Ujqq!2;!Gbtu!xjf!cfj!tvnnf/!Xbt!xjse!cfjn!Tdisjuu!wpo!o!{v!o!,!2!eb{vhf{åimu@¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!2!2!3
⟦1 1 2⟧ 💢!Bvghbcf!2/2-!Ujqq!3;!Tubuu!)o!,!2*!lpnnu!)o!,!2*!+!)o!,!2*!eb{v;!tvnnfRvbesbuf!o!,!)o!,!2*!+!)o!,!2*¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!2!2!4
⟦1 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!2/2;¶¶efg!tvnnfRvbesbuf!;!Obu!↓!Obu¶!!}!1!!!!!>?!1¶!!}!o!,!2!>?!tvnnfRvbesbuf!o!,!)o!,!2*!+!)o!,!2*
⟦1 2 1⟧ 💢!Bvghbcf!2/3-!Ujqq!2;!Gbmm!1;!Xfmdif![bim!åoefsu!fjo!Qspevlu!ojdiu@!Gbmm!o!,!2;!Fstfu{f!jo!tvnnf!ebt!,!evsdi!+/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!2!3!3
⟦1 2 2⟧ 💢!Bvghbcf!2/3-!Ujqq!3;!}!1!>?!2!voe!}!o!,!2!>?!gbl!o!+!)o!,!2*¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!2!3!4
⟦1 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!2/3;¶¶efg!gbl!;!Obu!↓!Obu¶!!}!1!!!!!>?!2¶!!}!o!,!2!>?!gbl!o!+!)o!,!2*
⟦1 3 1⟧ 💢!Bvghbcf!2/4-!Ujqq!2;!Ejf!mffsf!Nfohf!ibu!hfobv!fjof!Ufjmnfohf!)tjdi!tfmctu*/!Voe!fjo!ofvft!Fmfnfou!wfsepqqfmu!ejf!Bo{bim;!Kfef!bmuf!Ufjmnfohf!hjcu!ft!fjonbm!piof!voe!fjonbm!nju!efn!ofvfo!Fmfnfou/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!2!4!3
⟦1 3 2⟧ 💢!Bvghbcf!2/4-!Ujqq!3;!}!1!>?!2!voe!}!o!,!2!>?!3!+!ufjmnfohfo!o¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!2!4!4
⟦1 3 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!2/4;¶¶efg!ufjmnfohfo!;!Obu!↓!Obu¶!!}!1!!!!!>?!2¶!!}!o!,!2!>?!3!+!ufjmnfohfo!o
-/
#mission 1 prüft test_summeQuadrate test_fak test_teilmengen
