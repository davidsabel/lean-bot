import Lean
/-
  Mission 0: Hallo Lean!
  ======================
  Hängst du fest? Unter jeder Aufgabe steht eine Zeile wie  -- #tipp 0 1
  Lösche die zwei Striche am Anfang: Rechts erscheint Tipp 1.
  Mit  #tipp 0 1 2  kommt Tipp 2, mit  #tipp 0 1 3  die Lösung dieser Aufgabe.

  Lean ist eine Programmiersprache. Rechts im Fenster siehst du,
  was Lean zu jeder Zeile sagt. Klicke auf eine Zeile mit #eval.

  In jeder Mission findest du Beispiele und Aufgaben (✏️). Ersetze in den
  Aufgaben jedes `sorry`. Lean zeigt dir sofort, ob es passt.
-/

/- ⚙️ Tipp-Werkzeug (bitte nicht ändern). Weiter unten geht es los! -/
open Lean Elab Command in
elab "#tipp " m:num a:num s:(num)? : command => do
  let marke := s!"⟦{m.getNat} {a.getNat} {(s.map (·.getNat)).getD 1}⟧ "
  match ((← getFileMap).source.splitOn "\n").find? (·.startsWith marke) with
  | some z => logInfo (String.mk ((z.toList.drop marke.length).map fun c => if c == '¶' then '\n' else Char.ofNat (c.toNat - 1)))
  | none => logWarning "Diesen Tipp gibt es nicht."

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
#mission 0 prüft test_verdreifache test_flaeche test_quadrat test_bewertung
