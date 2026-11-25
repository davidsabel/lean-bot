import Lean
/-
  Mission 0: Hallo Lean!
  ======================
  Willkommen beim Lean-Bot: Beweisen ist Programmieren!
  ─────────────────────────────────────────────────────
  Du programmierst gern? Dann kannst du auch beweisen.

  Lean ist eine Programmiersprache, in der man nicht nur Programme schreibt,
  sondern auch beweist, dass sie stimmen. Ein Beweis ist in Lean ein Programm,
  und Lean prüft es so streng wie ein Compiler. Mit genau diesem Werkzeug wurde
  im November 2026 ein Beweis der Riemannschen Vermutung geprüft, eines der
  berühmtesten offenen Probleme der Mathematik.

  • Keine Installation: Alles läuft hier im Browser.
  • Kleine Schritte: sechs Missionen, jede dauert etwa 20 bis 40 Minuten.
  • Sofortige Rückmeldung: Rechts im Fenster sagt Lean dir, ob dein Beweis stimmt.
  • Vorwissen: etwas Programmiererfahrung. Die Mathematik (Logik, Quantoren,
    Induktion) wird jeweils kurz erklärt.

  Die Missionen:
    0  Hallo Lean: rechnen, Funktionen, erster Beweis
    1  Rekursion und Tests                 (Anzahl der Teilmengen)
    2  Beweise sind Programme              (Aussagenlogik)
    3  Quantoren                           (Prädikatenlogik, Gegenbeispiele)
    4  Induktion ist Rekursion             (vollständige Induktion)
    5  Ausblick: Mathlib, Euklid, Riemann  (Primzahlen, Widerspruchsbeweis)
  Am Ende jeder Mission bekommst du den Link zur nächsten.

  Zwei Hinweise zum Editor:
  • Beim ersten Öffnen erscheint rechts oben "Can I Trust This Proof?".
    Klicke auf "Don't show this again". Der Hinweis hat einen ernsten
    Hintergrund: Lean prüft, ob ein Beweis stimmt, aber nicht, ob die Aussage
    die gemeinte ist. Fremden Beweisen sollte man nicht blind vertrauen.
  • Lade die Seite nicht neu, sonst ist deine Arbeit weg. Kopiere sie
    vorher in eine Datei, wenn du eine Pause machst.

  So geht es:
    🏁  Scrolle nach unten zur Flagge 🏁. Dort beginnt die Mission.
        (Darüber stehen nur Werkzeuge, die musst du nicht lesen.)
    ✏️  Bei jeder Aufgabe ersetzt du `sorry` durch deine Lösung.
        Rechts im Fenster zeigt Lean sofort, ob es passt.
    💡  Hängst du fest? Unter jeder Aufgabe steht eine Zeile wie  -- #tipp 0 1
        Lösche die zwei Striche am Anfang, dann erscheint rechts Tipp 1.
        #tipp 0 1 2 gibt Tipp 2, #tipp 0 1 3 die Lösung dieser Aufgabe.
    ✅  Ganz unten steht die Prüfstation. Klicke auf die Zeile #mission:
        Rechts steht, was noch offen ist, oder der Link zur nächsten Mission.

  Lean ist eine Programmiersprache. Rechts im Fenster siehst du,
  was Lean zu jeder Zeile sagt. Klicke auf eine Zeile mit #eval.
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

-- Rechnen
#eval 2 + 3 * 4
#eval "Discrete " ++ "Droid " ++ "Academy"

/- ─────────────────────────────────────────────────────────────
  Schritt 1: eine eigene Funktion
──────────────────────────────────────────────────────────────── -/

-- Beispiel: Ein Droide verdoppelt seine Energie.
def verdopple (n : Nat) : Nat := 2 * n

#eval verdopple 21     -- 42

-- Das Besondere an Lean: Wir können nicht nur testen, sondern BEWEISEN.
-- `rfl` heißt: "einfach ausrechnen, dann sieht man es".
theorem test_verdopple : verdopple 21 = 42 := rfl

-- ✏️ Aufgabe 0.1: Ein Droide verdreifacht seine Energie.
def verdreifache (n : Nat) : Nat := sorry
-- #tipp 0 1

#eval verdreifache 5   -- soll 15 ergeben
theorem test_verdreifache : verdreifache 5 = 15 := rfl

/- ─────────────────────────────────────────────────────────────
  Schritt 2: Funktionen mit zwei Argumenten
──────────────────────────────────────────────────────────────── -/

-- Beispiel
def energie (kerne : Nat) (proKern : Nat) : Nat := kerne * proKern

#eval energie 5 12     -- 60

-- ✏️ Aufgabe 0.2: die Fläche eines Rechtecks
def flaeche (breite : Nat) (hoehe : Nat) : Nat := sorry
-- #tipp 0 2

theorem test_flaeche : flaeche 3 4 = 12 := rfl

-- ✏️ Aufgabe 0.3: Diesmal schreibst du die ganze Zeile nach `:=` selbst.
-- `quadrat n` soll n * n berechnen.
def quadrat (n : Nat) : Nat := sorry
-- #tipp 0 3

#eval quadrat 7        -- soll 49 ergeben
theorem test_quadrat : quadrat 0 = 0 ∧ quadrat 3 = 9 ∧ quadrat 7 = 49 := ⟨rfl, rfl, rfl⟩

/- ─────────────────────────────────────────────────────────────
  Schritt 3: Fallunterscheidung
──────────────────────────────────────────────────────────────── -/

-- Beispiel: Ladestand als Ampel
def ampel (n : Nat) : String :=
  if n < 30 then "rot" else if n < 70 then "gelb" else "grün"

#eval ampel 42         -- "gelb"

-- ✏️ Aufgabe 0.4: Ab 50 Punkten ist ein Test bestanden.
def bewertung (punkte : Nat) : String :=
  sorry
-- #tipp 0 4

theorem test_bewertung : bewertung 49 = "nicht bestanden" ∧ bewertung 50 = "bestanden" := ⟨rfl, rfl⟩

-- ✅ PRÜFSTATION: Klicke auf die nächste Zeile, rechts steht dann, wie es weitergeht.
#mission 0 prüft test_verdreifache test_flaeche test_quadrat test_bewertung
-- Geschafft? Weiter zu Mission 1 (Strg+Klick):
-- https://live.lean-lang.org/#url=https%3A%2F%2Fgithub.com%2Fdavidsabel%2Flean-bot%2Fblob%2Fmain%2Ffrei%2FM1_Rekursion.lean



/- Daten für Tipps und Prüfstation (verschlüsselt, bitte nicht ändern)
⟦0⟧ uftu`wfsesfjgbdif!uftu`gmbfdif!uftu`rvbesbu!uftu`cfxfsuvoh}Xfjufs!hfiu!ft!nju!Njttjpo!2;!Efs!Mjol!tufiu!jn!Fejups!ejsflu!voufs!efs![fjmf!$njttjpo!)Tush,Lmjdl*/
⟦0 1 1⟧ 💢!Bvghbcf!1/2-!Ujqq!2;!Tdibv!ejs!wfsepqqmf!bo/!Xbt!nvttu!ev!åoefso@¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!1!2!3
⟦0 1 2⟧ 💢!Bvghbcf!1/2-!Ujqq!3;!Tubuu!3!+!o!csbvditu!ev!4!+!o/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!1!2!4
⟦0 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!1/2;¶¶efg!wfsesfjgbdif!)o!;!Obu*!;!Obu!;>!4!+!o
⟦0 2 1⟧ 💢!Bvghbcf!1/3-!Ujqq!2;!Ejf!Gvolujpo!fofshjf!ibu!hfobv!efotfmcfo!Bvgcbv/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!1!3!3
⟦0 2 2⟧ 💢!Bvghbcf!1/3-!Ujqq!3;!Nvmujqmj{jfsf!ejf!cfjefo!Bshvnfouf;!csfjuf!+!ipfif/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!1!3!4
⟦0 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!1/3;¶¶efg!gmbfdif!)csfjuf!;!Obu*!)ipfif!;!Obu*!;!Obu!;>!csfjuf!+!ipfif
⟦0 3 1⟧ 💢!Bvghbcf!1/4-!Ujqq!2;!Fjo!Bshvnfou!xjf!cfj!wfsepqqmf-!bcfs!ejf![bim!xjse!nju!tjdi!tfmctu!nvmujqmj{jfsu/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!1!4!3
⟦0 3 2⟧ 💢!Bvghbcf!1/4-!Ujqq!3;!o!+!o¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!1!4!4
⟦0 3 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!1/4;¶¶efg!rvbesbu!)o!;!Obu*!;!Obu!;>!o!+!o
⟦0 4 1⟧ 💢!Bvghbcf!1/5-!Ujqq!2;!Xjf!bnqfm-!bcfs!nju!ovs!fjofn!jg!///!uifo!///!fmtf!////¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!1!5!3
⟦0 4 2⟧ 💢!Bvghbcf!1/5-!Ujqq!3;!jg!qvoluf!=!61!uifo!#ojdiu!cftuboefo#!fmtf!#cftuboefo#¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!1!5!4
⟦0 4 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!1/5;¶¶efg!cfxfsuvoh!)qvoluf!;!Obu*!;!Tusjoh!;>¶!!jg!qvoluf!=!61!uifo!#ojdiu!cftuboefo#!fmtf!#cftuboefo#
-/
