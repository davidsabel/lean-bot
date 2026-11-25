import Lean
/-
  Mission 2: Beweise sind Programme
  =================================
  So geht es:
    🏁  Scrolle nach unten zur Flagge 🏁. Dort beginnt die Mission.
        (Darüber stehen nur Werkzeuge, die musst du nicht lesen.)
    ✏️  Bei jeder Aufgabe ersetzt du `sorry` durch deine Lösung.
        Rechts im Fenster zeigt Lean sofort, ob es passt.
    💡  Hängst du fest? Unter jeder Aufgabe steht eine Zeile wie  -- #tipp 2 1
        Lösche die zwei Striche am Anfang, dann erscheint rechts Tipp 1.
        #tipp 2 1 2 gibt Tipp 2, #tipp 2 1 3 die Lösung dieser Aufgabe.
    ✅  Ganz unten steht die Prüfstation. Klicke auf die Zeile #mission:
        Rechts steht, was noch offen ist, oder dein Code für ILIAS.

  In Lean ist eine Aussage ein TYP und ein Beweis ist ein WERT dieses Typs.
  Eine Aussage zu beweisen heißt also: ein Programm schreiben, das den
  passenden Typ hat. Lean prüft den Typ, genau wie ein Compiler.

  Übersetzungstabelle (Logik  ↔  Programmieren):
    A → B      Funktion, die aus einem Beweis von A einen Beweis von B macht
    A ∧ B      Paar ⟨a, b⟩ aus einem Beweis von A und einem von B
    A ∨ B      entweder links (Or.inl a) oder rechts (Or.inr b)
    ¬A         Funktion A → False ("aus A folgt Unsinn")
-/

/- ⚙️ Werkzeuge für Tipps und Prüfstation (bitte nicht ändern). Weiter unten bei 🏁 geht es los! -/
open Lean Elab Command in
def daten (marke : String) : CommandElabM (Option String) := do
  let z? := ((← getFileMap).source.splitOn "\n").find? (·.startsWith marke)
  return z?.map fun z => String.ofList ((z.toList.drop marke.length).map fun c => if c == '¶' then '\n' else Char.ofNat (c.toNat - 1))
open Lean Elab Command in
elab "#tipp " m:num a:num s:(num)? : command => do
  match ← daten s!"⟦{m.getNat} {a.getNat} {(s.map (·.getNat)).getD 1}⟧ " with
  | some t => logInfo t
  | none => logWarning "Diesen Tipp gibt es nicht."
@[widget_module] def linkWidget : Lean.Widget.Module where
  javascript := "import * as React from 'react'; export default (p) => React.createElement('a', {href: p.url, target: '_blank'}, p.text)"
open Lean Elab Command in
elab "#mission " n:num " prüft " ids:ident* : command => do
  let some d ← daten s!"⟦{n.getNat}⟧ " | logWarning "Prüfdaten fehlen."
  let teile : List String := d.splitOn "|"
  let (soll, erfolg) := (teile.getD 0 "", teile.getD 1 "")
  if ids.toList.map (·.getId.toString) != soll.splitOn " " then
    logWarning "⚠️ Die Zeile #mission wurde verändert. Bitte die Datei neu öffnen."; return
  let mut offen := #[]
  for id in ids do
    if (← getEnv).find? id.getId |>.isNone then offen := offen.push s!"{id.getId} (fehlt)"
    else if (← Lean.collectAxioms id.getId).contains ``sorryAx then offen := offen.push s!"{id.getId}"
  if offen.isEmpty then
    logInfo m!"✅ Mission {n.getNat} geschafft!\n{erfolg}"
    if let some url := teile[2]? then
      let props := Json.mkObj [("url", toJson url), ("text", toJson "▶ Hier klicken: weiter zur nächsten Mission")]
      logInfo (.ofWidget { id := ``linkWidget, javascriptHash := linkWidget.javascriptHash, props := pure props } m!"{url}")
  else logWarning m!"⏳ Mission {n.getNat} ist noch nicht fertig.\nNoch offen: {", ".intercalate offen.toList}"

/- ═════════════════════════════════════════════════════════════
   🏁 START: Hier geht die Mission los!
   ═════════════════════════════════════════════════════════════ -/

/- ─────────────────────────────────────────────────────────────
  Schritt 1: Implikation = Funktion
──────────────────────────────────────────────────────────────── -/

-- Beispiel: A → A. Die Identitätsfunktion ist ein Beweis!
theorem beispiel_id (A : Prop) : A → A :=
  fun a => a

-- Beispiel: A → B → B. Eine Funktion mit zwei Argumenten, die das zweite zurückgibt.
-- `_` heißt: Dieses Argument wird nicht gebraucht.
theorem beispiel_zweites (A B : Prop) : A → B → B :=
  fun _ b => b

-- ✏️ Aufgabe 2.1: A → B → A
theorem aufgabe_2_1 (A B : Prop) : A → B → A :=
  sorry
-- #tipp 2 1

-- Beispiel: Modus ponens. Eine Funktion f : A → B auf a : A anwenden.
theorem beispiel_mp (A B : Prop) : (A → B) → A → B :=
  fun f a => f a

-- ✏️ Aufgabe 2.2: Kettenschluss
theorem aufgabe_2_2 (A B C : Prop) : (A → B) → (B → C) → A → C :=
  sorry
-- #tipp 2 2

/- ─────────────────────────────────────────────────────────────
  Schritt 2: Und = Paar
──────────────────────────────────────────────────────────────── -/

-- Beispiel: A ∧ B → B ∧ A. Paar auspacken und vertauscht wieder einpacken.
theorem beispiel_und (A B : Prop) : A ∧ B → B ∧ A :=
  fun ⟨a, b⟩ => ⟨b, a⟩

-- ✏️ Aufgabe 2.3: A ∧ B → A
theorem aufgabe_2_3 (A B : Prop) : A ∧ B → A :=
  sorry
-- #tipp 2 3

-- ✏️ Aufgabe 2.4: A → B → A ∧ B
theorem aufgabe_2_4 (A B : Prop) : A → B → A ∧ B :=
  sorry
-- #tipp 2 4

/- ─────────────────────────────────────────────────────────────
  Schritt 3: Oder = einer von zwei Fällen
──────────────────────────────────────────────────────────────── -/

-- Beispiel: A → A ∨ B. Man wählt die linke Seite.
theorem beispiel_links (A B : Prop) : A → A ∨ B :=
  fun a => Or.inl a

-- ✏️ Aufgabe 2.5: B → A ∨ B
theorem aufgabe_2_5 (A B : Prop) : B → A ∨ B :=
  sorry
-- #tipp 2 5

-- Beispiel: A ∨ B → B ∨ A. Fallunterscheidung mit match.
theorem beispiel_oder (A B : Prop) : A ∨ B → B ∨ A :=
  fun h => match h with
    | Or.inl a => Or.inr a
    | Or.inr b => Or.inl b

-- ✏️ Aufgabe 2.6: A ∨ A → A
theorem aufgabe_2_6 (A : Prop) : A ∨ A → A :=
  sorry
-- #tipp 2 6

/- ─────────────────────────────────────────────────────────────
  Schritt 4: Nicht = Funktion nach False
──────────────────────────────────────────────────────────────── -/

-- Beispiel: A → ¬A → False. ¬A ist eine Funktion A → False, man wendet sie auf a an.
theorem beispiel_nicht (A : Prop) : A → ¬A → False :=
  fun a na => na a

-- ✏️ Aufgabe 2.7: A → ¬¬A
-- ¬¬A bedeutet ¬A → False. Also ist das wieder eine Funktion mit zwei Argumenten.
theorem aufgabe_2_7 (A : Prop) : A → ¬¬A :=
  sorry
-- #tipp 2 7

/- ─────────────────────────────────────────────────────────────
  Schritt 5: Taktik-Modus
──────────────────────────────────────────────────────────────── -/
/-
  Statt das Programm direkt hinzuschreiben, kann man es Schritt für Schritt
  bauen lassen. Nach `by` stehen Befehle (Taktiken). Klicke auf die Zeilen:
  Rechts siehst du jeweils, was noch zu zeigen ist (das "Ziel").
    intro h        nimm die Voraussetzung h an (baut fun h => ...)
    exact t        das Ziel ist genau t
    constructor    Ziel A ∧ B in zwei Ziele A und B zerlegen
    cases h with   Fallunterscheidung über h : A ∨ B
    left / right   Ziel A ∨ B: zeige A bzw. B
-/

-- Beispiel: A ∧ B → B ∧ A mit Taktiken
theorem beispiel_taktik_und (A B : Prop) : A ∧ B → B ∧ A := by
  intro h
  constructor
  · exact h.2
  · exact h.1

-- Beispiel: A ∨ B → B ∨ A mit Taktiken
theorem beispiel_taktik_oder (A B : Prop) : A ∨ B → B ∨ A := by
  intro h
  cases h with
  | inl a => right; exact a
  | inr b => left; exact b

-- ✏️ Aufgabe 2.8: Distributivgesetz. Das Gerüst ist schon da.
theorem aufgabe_2_8 (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
  intro ⟨a, h⟩
  cases h with
  | inl b => sorry
  | inr c => sorry
-- #tipp 2 8

-- ✏️ Aufgabe 2.9: De Morgan, eine Richtung
theorem aufgabe_2_9 (A B : Prop) : ¬(A ∨ B) → ¬A ∧ ¬B := by
  sorry
-- #tipp 2 9

-- ✅ PRÜFSTATION: Klicke auf die nächste Zeile, rechts steht dann dein Code für ILIAS.
#mission 2 prüft aufgabe_2_1 aufgabe_2_2 aufgabe_2_3 aufgabe_2_4 aufgabe_2_5 aufgabe_2_6 aufgabe_2_7 aufgabe_2_8 aufgabe_2_9



/- Daten für Tipps und Prüfstation (verschlüsselt, bitte nicht ändern)
⟦2⟧ bvghbcf`3`2!bvghbcf`3`3!bvghbcf`3`4!bvghbcf`3`5!bvghbcf`3`6!bvghbcf`3`7!bvghbcf`3`8!bvghbcf`3`9!bvghbcf`3`:}Efjo!Dpef!gýs!JMJBT;!MFNNB.4DY4N
⟦2 1 1⟧ 💢!Bvghbcf!3/2-!Ujqq!2;!Hfobv!xjf!cfjtqjfm`{xfjuft-!ovs!xjse!ejftnbm!ebt!FSTUF!Bshvnfou!{vsýdlhfhfcfo/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!2!3
⟦2 1 2⟧ 💢!Bvghbcf!3/2-!Ujqq!3;!gvo!b!`!>?!b¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!2!4
⟦2 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!3/2;¶¶uifpsfn!bvghbcf`3`2!)B!C!;!Qspq*!;!B!↓!C!↓!B!;>¶!!gvo!b!`!>?!b
⟦2 2 1⟧ 💢!Bvghbcf!3/3-!Ujqq!2;!Esfj!Bshvnfouf;!g!;!B!↓!C-!h!;!C!↓!D!voe!b!;!B/!Xjf!cfj!cfjtqjfm`nq!xfoefu!nbo!Gvolujpofo!bo-!ejftnbm!{xfj!ijoufsfjoboefs/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!3!3
⟦2 2 2⟧ 💢!Bvghbcf!3/3-!Ujqq!3;!Bvt!b!nbdiu!g!fjofo!Cfxfjt!wpo!C-!ebsbvt!nbdiu!h!fjofo!Cfxfjt!wpo!D;!gvo!g!h!b!>?!h!)g!b*¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!3!4
⟦2 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!3/3;¶¶uifpsfn!bvghbcf`3`3!)B!C!D!;!Qspq*!;!)B!↓!C*!↓!)C!↓!D*!↓!B!↓!D!;>¶!!gvo!g!h!b!>?!h!)g!b*
⟦2 3 1⟧ 💢!Bvghbcf!3/4-!Ujqq!2;!Qbbs!bvtqbdlfo!xjf!jo!cfjtqjfm`voe-!eboo!ovs!efo!fjofo!Ufjm!{vsýdlhfcfo/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!4!3
⟦2 3 2⟧ 💢!Bvghbcf!3/4-!Ujqq!3;!gvo!⟩b-!`⟪!>?!b!)efs!{xfjuf!Ufjm!xjse!ojdiu!hfcsbvdiu-!ebsvn!`*¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!4!4
⟦2 3 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!3/4;¶¶uifpsfn!bvghbcf`3`4!)B!C!;!Qspq*!;!B!∨!C!↓!B!;>¶!!gvo!⟩b-!`⟪!>?!b
⟦2 4 1⟧ 💢!Bvghbcf!3/5-!Ujqq!2;![xfj!Bshvnfouf!xjf!jo!cfjtqjfm`{xfjuft/![vsýdlhfhfcfo!xjse!fjo!Qbbs!xjf!jo!cfjtqjfm`voe/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!5!3
⟦2 4 2⟧ 💢!Bvghbcf!3/5-!Ujqq!3;!gvo!b!c!>?!⟩b-!c⟪¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!5!4
⟦2 4 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!3/5;¶¶uifpsfn!bvghbcf`3`5!)B!C!;!Qspq*!;!B!↓!C!↓!B!∨!C!;>¶!!gvo!b!c!>?!⟩b-!c⟪
⟦2 5 1⟧ 💢!Bvghbcf!3/6-!Ujqq!2;!Ejftnbm!jtu!ejf!SFDIUF!Tfjuf!cfxjftfo/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!6!3
⟦2 5 2⟧ 💢!Bvghbcf!3/6-!Ujqq!3;!gvo!c!>?!Ps/jos!c¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!6!4
⟦2 5 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!3/6;¶¶uifpsfn!bvghbcf`3`6!)B!C!;!Qspq*!;!C!↓!B!∩!C!;>¶!!gvo!c!>?!Ps/jos!c
⟦2 6 1⟧ 💢!Bvghbcf!3/7-!Ujqq!2;!Gbmmvoufstdifjevoh!xjf!jo!cfjtqjfm`pefs/!Jo!cfjefo!Gåmmfo!ibtu!ev!fjofo!Cfxfjt!wpo!B/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!7!3
⟦2 6 2⟧ 💢!Bvghbcf!3/7-!Ujqq!3;!gvo!i!>?!nbudi!i!xjui!}!Ps/jom!b!>?!b!}!Ps/jos!b!>?!b!){xfj![fjmfo!xjf!jn!Cfjtqjfm*¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!7!4
⟦2 6 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!3/7;¶¶uifpsfn!bvghbcf`3`7!)B!;!Qspq*!;!B!∩!B!↓!B!;>¶!!gvo!i!>?!nbudi!i!xjui¶!!!!}!Ps/jom!b!>?!b¶!!!!}!Ps/jos!b!>?!b
⟦2 7 1⟧ 💢!Bvghbcf!3/8-!Ujqq!2;!Tdisfjcf!ft!hfobvtp!ijo!xjf!cfjtqjfm`ojdiu/!Mfbo!tjfiu-!ebtt!efs!Uzq!efstfmcf!jtu/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!8!3
⟦2 7 2⟧ 💢!Bvghbcf!3/8-!Ujqq!3;!gvo!b!ob!>?!ob!b¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!8!4
⟦2 7 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!3/8;¶¶uifpsfn!bvghbcf`3`8!)B!;!Qspq*!;!B!↓!­­B!;>¶!!gvo!b!ob!>?!ob!b
⟦2 8 1⟧ 💢!Bvghbcf!3/9-!Ujqq!2;!Jn!fstufo!Gbmm!ibtu!ev!b!;!B!voe!c!;!C-!jn!{xfjufo!b!;!B!voe!d!;!D/!Xåimf!nju!mfgu!pefs!sjhiu!ejf!qbttfoef!Tfjuf-!xjf!jo!cfjtqjfm`ublujl`pefs/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!9!3
⟦2 8 2⟧ 💢!Bvghbcf!3/9-!Ujqq!3;!}!jom!c!>?!mfgu<!fybdu!⟩b-!c⟪!voe!}!jos!d!>?!sjhiu<!fybdu!⟩b-!d⟪¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!9!4
⟦2 8 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!3/9;¶¶uifpsfn!bvghbcf`3`9!)B!C!D!;!Qspq*!;!B!∨!)C!∩!D*!↓!)B!∨!C*!∩!)B!∨!D*!;>!cz¶!!jousp!⟩b-!i⟪¶!!dbtft!i!xjui¶!!}!jom!c!>?!mfgu<!fybdu!⟩b-!c⟪¶!!}!jos!d!>?!sjhiu<!fybdu!⟩b-!d⟪
⟦2 9 1⟧ 💢!Bvghbcf!3/:-!Ujqq!2;!Cfhjoof!nju!jousp!i!voe!dpotusvdups!xjf!jo!cfjtqjfm`ublujl`voe/!Eboo!jtu!{/C/!­B!{v!{fjhfo-!bmtp!fjof!Gvolujpo;!jousp!b/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!:!3
⟦2 9 2⟧ 💢!Bvghbcf!3/:-!Ujqq!3;!Nju!b!;!B!ibtu!ev!Ps/jom!b!;!B!∩!C-!voe!i!nbdiu!ebsbvt!Gbmtf;!fybdu!i!)Ps/jom!b*/!Gýs!C!hfobvtp!nju!Ps/jos/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!:!4
⟦2 9 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!3/:;¶¶uifpsfn!bvghbcf`3`:!)B!C!;!Qspq*!;!­)B!∩!C*!↓!­B!∨!­C!;>!cz¶!!jousp!i¶!!dpotusvdups¶!!¸!jousp!b<!fybdu!i!)Ps/jom!b*¶!!¸!jousp!c<!fybdu!i!)Ps/jos!c*
-/
