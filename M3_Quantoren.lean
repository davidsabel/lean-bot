import Lean
/-
  Mission 3: Quantoren
  ====================
  Hängst du fest? Unter jeder Aufgabe steht eine Zeile wie  -- #tipp 3 1
  Lösche die zwei Striche am Anfang: Rechts erscheint Tipp 1.
  Mit  #tipp 3 1 2  kommt Tipp 2, mit  #tipp 3 1 3  die Lösung dieser Aufgabe.

  ∃ x, P x    ist ein Paar ⟨x, Beweis⟩: ein Zeuge x und der Beweis, dass P x gilt.
  ∀ x, P x    ist eine Funktion: Sie bekommt ein x und liefert einen Beweis von P x.

  Zwei hilfreiche Taktiken:
    decide   rechnet endliche Fragen mit konkreten Zahlen aus
    omega    löst lineare Gleichungen und Ungleichungen über Nat automatisch
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
  Schritt 1: Es gibt ... (Zeuge angeben)
──────────────────────────────────────────────────────────────── -/

-- Beispiel: Zeuge 7, den Rest rechnet Lean aus.
theorem beispiel_existiert : ∃ n : Nat, n * n = 49 := ⟨7, rfl⟩

-- ✏️ Aufgabe 3.1: Es gibt ein n mit n + n = 26.
theorem aufgabe_3_1 : ∃ n : Nat, n + n = 26 := sorry
-- #tipp 3 1

-- Eine eigene Aussageform: n ist gerade, wenn n = 2 * k für ein k.
def gerade (n : Nat) : Prop := ∃ k, n = 2 * k

-- Beispiel
theorem beispiel_gerade : gerade 10 := ⟨5, rfl⟩

-- ✏️ Aufgabe 3.2: 42 ist gerade.
theorem aufgabe_3_2 : gerade 42 := sorry
-- #tipp 3 2

/- ─────────────────────────────────────────────────────────────
  Schritt 2: Für alle ... (eine Funktion)
──────────────────────────────────────────────────────────────── -/

-- Beispiel: 4n ist immer gerade. Für jedes n ist 2n der Zeuge, omega rechnet nach.
theorem beispiel_alle : ∀ n : Nat, gerade (4 * n) :=
  fun n => ⟨2 * n, by omega⟩

-- ✏️ Aufgabe 3.3: 2n ist immer gerade.
theorem aufgabe_3_3 : ∀ n : Nat, gerade (2 * n) :=
  sorry
-- #tipp 3 3

-- Beispiel: Ist n gerade, dann auch n + 4. Mit Taktiken:
theorem beispiel_plus4 : ∀ n : Nat, gerade n → gerade (n + 4) := by
  intro n h
  obtain ⟨k, hk⟩ := h        -- h auspacken: hk : n = 2 * k
  exact ⟨k + 2, by omega⟩    -- n + 4 = 2 * (k + 2)

-- ✏️ Aufgabe 3.4: Ist n gerade, dann auch n + 2.
theorem aufgabe_3_4 : ∀ n : Nat, gerade n → gerade (n + 2) := by
  sorry
-- #tipp 3 4

/- ─────────────────────────────────────────────────────────────
  Schritt 3: Gegenbeispiele
──────────────────────────────────────────────────────────────── -/
/-
  Beispiele sind kein Beweis! Für n = 0, 1, ..., 39 ist n*n + n + 41 eine Primzahl,
  aber nicht für alle n. Einen ∀-Satz widerlegt man durch EIN Gegenbeispiel.
-/

-- Beispiel: Widerlege "Jede natürliche Zahl ist kleiner als 10".
theorem beispiel_gegen : ¬ (∀ n : Nat, n < 10) := by
  intro h            -- angenommen, es gilt für alle n ...
  have h10 := h 10   -- ... dann auch für 10: h10 : 10 < 10
  omega              -- Widerspruch

-- ✏️ Aufgabe 3.5: Widerlege "Jede natürliche Zahl ist kleiner als 100".
theorem aufgabe_3_5 : ¬ (∀ n : Nat, n < 100) := by
  sorry
-- #tipp 3 5

-- ✏️ Aufgabe 3.6: Widerlege "Jede natürliche Zahl ist gerade".
theorem aufgabe_3_6 : ¬ (∀ n : Nat, gerade n) := by
  sorry
-- #tipp 3 6

-- ✅ PRÜFSTATION: Klicke auf die nächste Zeile, rechts steht dann dein Code für ILIAS.
#mission 3 prüft aufgabe_3_1 aufgabe_3_2 aufgabe_3_3 aufgabe_3_4 aufgabe_3_5 aufgabe_3_6



/- Daten für Tipps und Prüfstation (verschlüsselt, bitte nicht ändern)
⟦3⟧ bvghbcf`4`2!bvghbcf`4`3!bvghbcf`4`4!bvghbcf`4`5!bvghbcf`4`6!bvghbcf`4`7}MFNNB.8DGBM
⟦3 1 1⟧ 💢!Bvghbcf!4/2-!Ujqq!2;!Xfmdif![bim!jtu!efs![fvhf@!Eboo!xjf!jn!Cfjtqjfm;!⟩[fvhf-!sgm⟪/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!2!3
⟦3 1 2⟧ 💢!Bvghbcf!4/2-!Ujqq!3;!⟩24-!sgm⟪¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!2!4
⟦3 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!4/2;¶¶uifpsfn!bvghbcf`4`2!;!∄!o!;!Obu-!o!,!o!>!37!;>!⟩24-!sgm⟪
⟦3 2 1⟧ 💢!Bvghbcf!4/3-!Ujqq!2;!53!>!3!+!l/!Xfmdift!l@¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!3!3
⟦3 2 2⟧ 💢!Bvghbcf!4/3-!Ujqq!3;!⟩32-!sgm⟪¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!3!4
⟦3 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!4/3;¶¶uifpsfn!bvghbcf`4`3!;!hfsbef!53!;>!⟩32-!sgm⟪
⟦3 3 1⟧ 💢!Bvghbcf!4/4-!Ujqq!2;!Xjf!jn!Cfjtqjfm/!Xfmdifs![fvhf!l!fsgýmmu!3!+!o!>!3!+!l@¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!4!3
⟦3 3 2⟧ 💢!Bvghbcf!4/4-!Ujqq!3;!gvo!o!>?!⟩o-!cz!pnfhb⟪¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!4!4
⟦3 3 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!4/4;¶¶uifpsfn!bvghbcf`4`4!;!∁!o!;!Obu-!hfsbef!)3!+!o*!;>¶!!gvo!o!>?!⟩o-!cz!pnfhb⟪
⟦3 4 1⟧ 💢!Bvghbcf!4/5-!Ujqq!2;!Ejf!fstufo!{xfj![fjmfo!tjoe!hfobv!xjf!jn!Cfjtqjfm/!Ovs!efs![fvhf!åoefsu!tjdi/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!5!3
⟦3 4 2⟧ 💢!Bvghbcf!4/5-!Ujqq!3;!Bvt!o!>!3!+!l!gpmhu!o!,!3!>!3!+!)l!,!2*/!Mfu{uf![fjmf;!fybdu!⟩l!,!2-!cz!pnfhb⟪¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!5!4
⟦3 4 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!4/5;¶¶uifpsfn!bvghbcf`4`5!;!∁!o!;!Obu-!hfsbef!o!↓!hfsbef!)o!,!3*!;>!cz¶!!jousp!o!i¶!!pcubjo!⟩l-!il⟪!;>!i¶!!fybdu!⟩l!,!2-!cz!pnfhb⟪
⟦3 5 1⟧ 💢!Bvghbcf!4/6-!Ujqq!2;!Esfj![fjmfo!xjf!jn!Cfjtqjfm/!Xfmdif![bim!jtu!ebt!Hfhfocfjtqjfm@¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!6!3
⟦3 5 2⟧ 💢!Bvghbcf!4/6-!Ujqq!3;!jousp!i-!eboo!ibwf!i211!;>!i!211-!eboo!pnfhb¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!6!4
⟦3 5 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!4/6;¶¶uifpsfn!bvghbcf`4`6!;!­!)∁!o!;!Obu-!o!=!211*!;>!cz¶!!jousp!i¶!!ibwf!i211!;>!i!211¶!!pnfhb
⟦3 6 1⟧ 💢!Bvghbcf!4/7-!Ujqq!2;!Ebt!Hfhfocfjtqjfm!jtu!2/!Nju!jousp!i!xjf!pcfo!cflpnntu!ev!i!2!;!hfsbef!2/!Ebt!jtu!fjo!Qbbs-!ebt!nbo!nju!pcubjo!bvtqbdlfo!lboo!)xjf!jo!cfjtqjfm`qmvt5*/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!7!3
⟦3 6 2⟧ 💢!Bvghbcf!4/7-!Ujqq!3;!jousp!i-!eboo!pcubjo!⟩l-!il⟪!;>!i!2!)il!;!2!>!3!+!l*-!eboo!pnfhb¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!7!4
⟦3 6 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!4/7;¶¶uifpsfn!bvghbcf`4`7!;!­!)∁!o!;!Obu-!hfsbef!o*!;>!cz¶!!jousp!i¶!!pcubjo!⟩l-!il⟪!;>!i!2¶!!pnfhb
-/
