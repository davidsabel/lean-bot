import Lean
/-
  Mission 4: Induktion ist Rekursion
  ==================================
  Worum geht es? Ein Induktionsbeweis ist in Lean eine rekursive Funktion,
  die Beweise zurückgibt: Der Fall 0 ist der Induktionsanfang, im Fall n + 1
  ruft sich die Funktion selbst für n auf, das ist die Induktionshypothese.
  Damit beweist du zum ersten Mal etwas über dein eigenes Programm für ALLE
  Eingaben, nicht nur für ein paar Tests.

  So geht es:
    🏁  Scrolle nach unten zur Flagge 🏁. Dort beginnt die Mission.
        (Darüber stehen nur Werkzeuge, die musst du nicht lesen.)
    ✏️  Bei jeder Aufgabe ersetzt du `sorry` durch deine Lösung.
        Rechts im Fenster zeigt Lean sofort, ob es passt.
    💡  Hängst du fest? Unter jeder Aufgabe steht eine Zeile wie  -- #tipp 4 1
        Lösche die zwei Striche am Anfang, dann erscheint rechts Tipp 1.
        #tipp 4 1 2 gibt Tipp 2, #tipp 4 1 3 die Lösung dieser Aufgabe.
    ✅  Ganz unten steht die Prüfstation. Klicke auf die Zeile #mission:
        Rechts steht, was noch offen ist, oder der Link zur nächsten Mission.

  Tests prüfen einzelne Werte. Mit Induktion beweisen wir Aussagen für ALLE n.

  Ein Beweis durch Induktion ist eine REKURSIVE FUNKTION, die Beweise
  zurückgibt: Für 0 liefert sie den Induktionsanfang, für n + 1 benutzt sie
  den Beweis für n (das ist die Induktionshypothese!).
-/

/- ⚙️ Werkzeuge für Tipps und Prüfstation (bitte nicht ändern). Weiter unten bei 🏁 geht es los! -/
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
  let [soll, erfolg] := d.splitOn "|" | logWarning "Prüfdaten fehlen."
  if ids.toList.map (·.getId.toString) != soll.splitOn " " then
    logWarning "⚠️ Die Zeile #mission wurde verändert. Bitte die Datei neu öffnen."; return
  let mut offen := #[]
  for id in ids do
    if (← getEnv).find? id.getId |>.isNone then offen := offen.push s!"{id.getId} (fehlt)"
    else if (← Lean.collectAxioms id.getId).contains ``sorryAx then offen := offen.push s!"{id.getId}"
  if offen.isEmpty then logInfo m!"✅ Mission {n.getNat} geschafft!\n{erfolg}"
  else logWarning m!"⏳ Mission {n.getNat} ist noch nicht fertig.\nNoch offen: {", ".intercalate offen.toList}"

/- ═════════════════════════════════════════════════════════════
   🏁 START: Hier geht die Mission los!
   ═════════════════════════════════════════════════════════════ -/

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
  | succ n ih =>                -- ih ist die Induktionshypothese für n
      simp only [summe]         -- summe (n + 1) durch seine Definition ersetzen
      grind                     -- den Rest (Rechnen mit ih) erledigt grind

-- ✏️ Aufgabe 4.1: die Summe der ersten n ungeraden Zahlen 1 + 3 + 5 + ...
def ungerade : Nat → Nat
  | 0     => 0
  | n + 1 => ungerade n + (2 * n + 1)

#eval ungerade 5     -- 25. Vermutung?

theorem ungerade_formel (n : Nat) : ungerade n = n * n := by
  sorry
-- #tipp 4 1

-- ✏️ Aufgabe 4.2: `teilmengen` aus Mission 1. Zeige teilmengen n = 2 ^ n.
def teilmengen : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * teilmengen n

theorem teilmengen_formel (n : Nat) : teilmengen n = 2 ^ n := by
  sorry
-- #tipp 4 2

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
  | cons x xs ih =>
      simp only [plusEins, List.length_cons, ih]

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

-- ✅ PRÜFSTATION: Klicke auf die nächste Zeile, rechts steht dann, wie es weitergeht.
#mission 4 prüft ungerade_formel teilmengen_formel laenge_bleibt summe_verdoppelt
-- Geschafft? Weiter zu Mission 5 (Strg+Klick):
-- https://live.lean-lang.org/#url=https%3A%2F%2Fgithub.com%2Fdavidsabel%2Flean-bot%2Fblob%2Fmain%2Ffrei%2FM5_Ausblick.lean



/- Daten für Tipps und Prüfstation (verschlüsselt, bitte nicht ändern)
⟦4⟧ vohfsbef`gpsnfm!ufjmnfohfo`gpsnfm!mbfohf`cmfjcu!tvnnf`wfsepqqfmu}Xfjufs!hfiu!ft!nju!Njttjpo!6;!Efs!Mjol!tufiu!jn!Fejups!ejsflu!voufs!efs![fjmf!$njttjpo!)Tush,Lmjdl*/
⟦4 1 1⟧ 💢!Bvghbcf!5/2-!Ujqq!2;!Efs!Cfxfjt!ibu!hfobv!efotfmcfo!Bvgcbv!xjf!hbvtt/!Lpqjfsf!jio!voe!qbttf!fjofo!Obnfo!bo/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!2!3
⟦4 1 2⟧ 💢!Bvghbcf!5/2-!Ujqq!3;!Jo!efs![fjmf!tjnq!pomz!\///^!nvtt!kfu{u!vohfsbef!tubuu!tvnnf!tufifo/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!2!4
⟦4 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!5/2;¶¶efg!vohfsbef!;!Obu!↓!Obu¶!!}!1!!!!!>?!1¶!!}!o!,!2!>?!vohfsbef!o!,!)3!+!o!,!2*
⟦4 2 1⟧ 💢!Bvghbcf!5/3-!Ujqq!2;!Xjfefs!efstfmcf!Bvgcbv!xjf!cfj!hbvtt/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!3!3
⟦4 2 2⟧ 💢!Bvghbcf!5/3-!Ujqq!3;!Jo!efs![fjmf!tjnq!pomz!\///^!tufiu!kfu{u!ufjmnfohfo/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!3!4
⟦4 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!5/3;¶¶efg!ufjmnfohfo!;!Obu!↓!Obu¶!!}!1!!!!!>?!2¶!!}!o!,!2!>?!3!+!ufjmnfohfo!o
⟦4 3 1⟧ 💢!Bvghbcf!5/4-!Ujqq!2;!Hfobv!xjf!qmvtFjot`mbfohf/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!4!3
⟦4 3 2⟧ 💢!Bvghbcf!5/4-!Ujqq!3;!Jo!efs![fjmf!tjnq!pomz!\///^!tufiu!kfu{u!wfsepqqmf!tubuu!qmvtFjot/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!4!4
⟦4 3 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!5/4;¶¶uifpsfn!mbfohf`cmfjcu!)yt!;!Mjtu!Obu*!;!)wfsepqqmf!yt*/mfohui!>!yt/mfohui!;>!cz¶!!joevdujpo!yt!xjui¶!!}!ojm!>?!sgm¶!!}!dpot!y!yt!ji!>?¶!!!!!!tjnq!pomz!\wfsepqqmf-!Mjtu/mfohui`dpot-!ji^
⟦4 4 1⟧ 💢!Bvghbcf!5/5-!Ujqq!2;!Joevlujpo!ýcfs!yt!xjf!fcfo/!Jn!Gbmm!dpot!ijmgu!Mjtu/tvn`dpot!)ejf!Tvnnf!wpo!y!;;!yt!jtu!y!,!Tvnnf!wpo!yt*/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!5!3
⟦4 4 2⟧ 💢!Bvghbcf!5/5-!Ujqq!3;!Gbmm!dpot!y!yt!ji;!tjnq!pomz!\wfsepqqmf-!Mjtu/tvn`dpot^!voe!ebobdi!hsjoe-!xjf!cfj!hbvtt/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!5!4
⟦4 4 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!5/5;¶¶uifpsfn!tvnnf`wfsepqqfmu!)yt!;!Mjtu!Obu*!;!)wfsepqqmf!yt*/tvn!>!3!+!yt/tvn!;>!cz¶!!joevdujpo!yt!xjui¶!!}!ojm!>?!sgm¶!!}!dpot!y!yt!ji!>?¶!!!!!!tjnq!pomz!\wfsepqqmf-!Mjtu/tvn`dpot^¶!!!!!!hsjoe
-/
