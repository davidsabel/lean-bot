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

-- ✅ PRÜFSTATION: Klicke auf die nächste Zeile, rechts steht dann dein Code für ILIAS.
#mission 4 prüft ungerade_formel teilmengen_formel laenge_bleibt summe_verdoppelt



/- Daten für Tipps und Prüfstation (verschlüsselt, bitte nicht ändern)
⟦4⟧ vohfsbef`gpsnfm!ufjmnfohfo`gpsnfm!mbfohf`cmfjcu!tvnnf`wfsepqqfmu}MFNNB.GYYQB
⟦4 1 1⟧ 💢!Bvghbcf!5/2-!Ujqq!2;!Efs!Cfxfjt!ibu!hfobv!efotfmcfo!Bvgcbv!xjf!hbvtt/!Lpqjfsf!jio!voe!qbttf!fjofo!Obnfo!bo/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!2!3
⟦4 1 2⟧ 💢!Bvghbcf!5/2-!Ujqq!3;!Jo!efs![fjmf!tjnq!pomz!\///^!nvtt!kfu{u!vohfsbef!tubuu!tvnnf!tufifo/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!2!4
⟦4 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!5/2;¶¶efg!vohfsbef!;!Obu!↓!Obu¶!!}!1!!!!!>?!1¶!!}!o!,!2!>?!vohfsbef!o!,!)3!+!o!,!2*
⟦4 2 1⟧ 💢!Bvghbcf!5/3-!Ujqq!2;!Xjfefs!efstfmcf!Bvgcbv!xjf!cfj!hbvtt/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!3!3
⟦4 2 2⟧ 💢!Bvghbcf!5/3-!Ujqq!3;!Jo!efs![fjmf!tjnq!pomz!\///^!tufiu!kfu{u!ufjmnfohfo/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!3!4
⟦4 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!5/3;¶¶efg!ufjmnfohfo!;!Obu!↓!Obu¶!!}!1!!!!!>?!2¶!!}!o!,!2!>?!3!+!ufjmnfohfo!o
⟦4 3 1⟧ 💢!Bvghbcf!5/4-!Ujqq!2;!Hfobv!xjf!qmvtFjot`mbfohf/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!4!3
⟦4 3 2⟧ 💢!Bvghbcf!5/4-!Ujqq!3;!Jo!efs![fjmf!tjnq!pomz!\///^!tufiu!kfu{u!wfsepqqmf!tubuu!qmvtFjot/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!4!4
⟦4 3 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!5/4;¶¶uifpsfn!mbfohf`cmfjcu!)yt!;!Mjtu!Obu*!;!)wfsepqqmf!yt*/mfohui!>!yt/mfohui!;>!cz¶!!joevdujpo!yt!xjui¶!!}!ojm!>?!sgm¶!!}!dpot!y!yt!jw!>?¶!!!!!!tjnq!pomz!\wfsepqqmf-!Mjtu/mfohui`dpot-!jw^
⟦4 4 1⟧ 💢!Bvghbcf!5/5-!Ujqq!2;!Joevlujpo!ýcfs!yt!xjf!fcfo/!Jn!Gbmm!dpot!ijmgu!Mjtu/tvn`dpot!)ejf!Tvnnf!wpo!y!;;!yt!jtu!y!,!Tvnnf!wpo!yt*/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!5!3
⟦4 4 2⟧ 💢!Bvghbcf!5/5-!Ujqq!3;!Gbmm!dpot!y!yt!jw;!tjnq!pomz!\wfsepqqmf-!Mjtu/tvn`dpot^!voe!ebobdi!hsjoe-!xjf!cfj!hbvtt/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!5!4
⟦4 4 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!5/5;¶¶uifpsfn!tvnnf`wfsepqqfmu!)yt!;!Mjtu!Obu*!;!)wfsepqqmf!yt*/tvn!>!3!+!yt/tvn!;>!cz¶!!joevdujpo!yt!xjui¶!!}!ojm!>?!sgm¶!!}!dpot!y!yt!jw!>?¶!!!!!!tjnq!pomz!\wfsepqqmf-!Mjtu/tvn`dpot^¶!!!!!!hsjoe
-/
