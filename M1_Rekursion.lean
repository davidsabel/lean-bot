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

/- ⚙️ Werkzeuge für Tipps und Prüfstation (bitte nicht ändern). Weiter unten geht es los! -/
open Lean Elab Command in
def daten (marke : String) : CommandElabM (Option String) := do
  let z? := ((← getFileMap).source.splitOn "\n").find? (·.startsWith marke)
  return z?.map fun z => String.mk ((z.toList.drop marke.length).map fun c => if c == '¶' then '\n' else Char.ofNat (c.toNat - 1))
open Lean Elab Command in
elab "#tipp " m:num a:num s:(num)? : command => do
  match ← daten s!"⟦{m.getNat} {a.getNat} {(s.map (·.getNat)).getD 1}⟧ " with
  | some t => logInfo t
  | none => logWarning "Diesen Tipp gibt es nicht."
open Lean Elab Command in
elab "#mission " n:num " prüft " ids:ident* : command => do
  let some d ← daten s!"⟦{n.getNat}⟧ " | logWarning "Prüfdaten fehlen."
  let [soll, code] := d.splitOn "|" | logWarning "Prüfdaten fehlen."
  if ids.toList.map (·.getId.toString) != soll.splitOn " " then
    logWarning "⚠️ Die Zeile #mission wurde verändert. Bitte die Datei neu öffnen."; return
  let mut offen := #[]
  for id in ids do
    if (← getEnv).find? id.getId |>.isNone then offen := offen.push s!"{id.getId} (fehlt)"
    else if (← Lean.collectAxioms id.getId).contains ``sorryAx then offen := offen.push s!"{id.getId}"
  if offen.isEmpty then logInfo m!"✅ Mission {n.getNat} geschafft!\nDein Code für ILIAS: {code}"
  else logWarning m!"⏳ Mission {n.getNat} ist noch nicht fertig.\nNoch offen: {", ".intercalate offen.toList}"

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

-- ✅ PRÜFSTATION: Klicke auf die nächste Zeile, rechts steht dann dein Code für ILIAS.
#mission 1 prüft test_summeQuadrate test_fak test_teilmengen



/- Daten für Tipps und Prüfstation (verschlüsselt, bitte nicht ändern)
⟦1⟧ uftu`tvnnfRvbesbuf!uftu`gbl!uftu`ufjmnfohfo}MFNNB.DQY:O
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
