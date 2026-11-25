import Mathlib
/-
  Mission 5: Ausblick, die große Bibliothek Mathlib
  =================================================
  Worum geht es? Mathlib ist eine riesige Bibliothek formal bewiesener
  Mathematik. Du siehst Euklids Beweis, dass es unendlich viele Primzahlen
  gibt, als Lean-Programm und findest die Aussage der Riemannschen
  Vermutung in der Bibliothek.
  Hinweis: Beim ersten Öffnen lädt der Editor die Bibliothek. Das kann
  ein bis zwei Minuten dauern.

  So geht es:
    🏁  Scrolle nach unten zur Flagge 🏁. Dort beginnt die Mission.
        (Darüber stehen nur Werkzeuge, die musst du nicht lesen.)
    ✏️  Bei jeder Aufgabe ersetzt du `sorry` durch deine Lösung.
        Rechts im Fenster zeigt Lean sofort, ob es passt.
    💡  Hängst du fest? Unter jeder Aufgabe steht eine Zeile wie  -- #tipp 5 1
        Lösche die zwei Striche am Anfang, dann erscheint rechts Tipp 1.
        #tipp 5 1 2 gibt Tipp 2, #tipp 5 1 3 die Lösung dieser Aufgabe.
    ✅  Ganz unten steht die Prüfstation. Klicke auf die Zeile #mission:
        Rechts steht, was noch offen ist, oder der Link zur nächsten Mission.

  Mathlib ist eine riesige Sammlung formal bewiesener Mathematik
  (über 250 000 Sätze), geschrieben von Hunderten Freiwilligen.
  Alles darin hat Lean geprüft. Du kannst die Sätze benutzen wie Bibliotheksfunktionen.
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

-- Was sagt ein Satz? #check zeigt die Aussage (den Typ):
#check Nat.exists_infinite_primes   -- Euklid: Über jeder Zahl liegt eine Primzahl

-- Mathlib-Taktiken rechnen für uns:
-- Beispiel
theorem beispiel_5_1 : Nat.Prime 101 := by norm_num

-- Den Satz von Euklid benutzen: Es gibt eine Primzahl größer als 1000.
theorem beispiel_5_2 : ∃ p, 1000 < p ∧ Nat.Prime p := by
  obtain ⟨p, hp, prim⟩ := Nat.exists_infinite_primes 1001
  exact ⟨p, by omega, prim⟩

/-
  Euklids Beweis Schritt für Schritt (ein Widerspruchsbeweis):
  Für n betrachte m = n! + 1 und einen Primteiler p von m.
  Wäre p ≤ n, dann teilt p auch n!, also teilt p die Differenz 1. Widerspruch.
-/
theorem euklid (n : Nat) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  let p := Nat.minFac (Nat.factorial n + 1)
  have prim : Nat.Prime p := Nat.minFac_prime (by
    have := Nat.factorial_pos n
    omega)
  refine ⟨p, ?_, prim⟩
  by_contra h
  have h1 : p ∣ Nat.factorial n := (Nat.Prime.dvd_factorial prim).mpr (by omega)
  have h2 : p ∣ Nat.factorial n + 1 := Nat.minFac_dvd _
  have h3 : p ∣ 1 := (Nat.dvd_add_right h1).mp h2
  exact Nat.Prime.one_lt prim |>.ne' (Nat.dvd_one.mp h3)

-- ✏️ Aufgabe 5.1: 2^7 - 1 = 127 ist eine Primzahl (eine Mersenne-Primzahl).
theorem beispiel_5_3 : Nat.Prime (2 ^ 7 - 1) := by
  sorry
-- #tipp 5 1

/-
  Und die Riemannsche Vermutung? Ihre Aussage steht in Mathlib:
-/
#check @RiemannHypothesis
#print RiemannHypothesis
/-
  Der Beweis vom November 2026 ist so lang, dass er nicht in dieses Fenster passt.
  Aber er ist in derselben Sprache geschrieben, die du gerade benutzt,
  und Lean hat ihn genauso geprüft wie deine kleinen Beweise hier.
-/

-- ✅ PRÜFSTATION: Klicke auf die nächste Zeile, rechts steht dann, wie es weitergeht.
#mission 5 prüft beispiel_5_3



/- Daten für Tipps und Prüfstation (verschlüsselt, bitte nicht ändern)
⟦5⟧ cfjtqjfm`6`4}🎊!Ev!ibtu!bmmf!Njttjpofo!hftdibggu/!Ifs{mjdifo!Hmýdlxvotdi"¶¶Xjf!hfiu!ft!xfjufs@!Lptufompt!bvg!mfbo.mboh/psh;¶‣!Gvodujpobm!Qsphsbnnjoh!jo!Mfbo;!Mfbo!bmt!Qsphsbnnjfstqsbdif¶‣!Nbuifnbujdt!jo!Mfbo;!Nbuifnbujl!nju!Nbuimjc¶‣!Uifpsfn!Qspwjoh!jo!Mfbo!5;!ejf!Mphjl!ijoufs!Mfbo¶‣!Obuvsbm!Ovncfs!Hbnf;!Sfdifosfhfmo!Tdisjuu!gýs!Tdisjuu!tfmctu!cfxfjtfo
⟦5 1 1⟧ 💢!Bvghbcf!6/2-!Ujqq!2;!Tdibv!ejs!cfjtqjfm`6`2!bo;!Epsu!{fjhu!fjof!fjo{jhf!Ublujl-!ebtt!212!fjof!Qsjn{bim!jtu/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!6!2!3
⟦5 1 2⟧ 💢!Bvghbcf!6/2-!Ujqq!3;!opsn`ovn¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!6!2!4
⟦5 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!6/2;¶¶uifpsfn!cfjtqjfm`6`4!;!Obu/Qsjnf!)3!_!8!.!2*!;>!cz¶!!opsn`ovn
-/
