import Mathlib
/-
  Beweismethoden mit Lean
  =======================
  Zum Kapitel "Beweise" der Vorlesung Diskrete Strukturen.

  Lean ist eine Programmiersprache, die Beweise Schritt für Schritt überprüft.
  In dieser Datei üben Sie die Beweismethoden aus der Vorlesung: direkter Beweis,
  Kontraposition, Widerspruch, Gegenbeispiel, Fallunterscheidung, Äquivalenz
  und vollständige Induktion. Vorkenntnisse in Lean brauchen Sie nicht.

  So geht es:
    🏁  Scrollen Sie nach unten zur Flagge 🏁. Dort geht es los.
    👀  Zu jeder Methode gibt es zuerst Beispiele. Klicken Sie in die Zeilen eines
        Beweises: Rechts sehen Sie, was gerade bekannt ist und was noch zu zeigen ist (⊢).
    ✏️  In den Aufgaben ersetzen Sie `sorry` durch Ihren Beweis.
    💡  Hängen Sie fest? Unter jeder Aufgabe steht eine Zeile wie  -- #tipp 1 1
        Löschen Sie die zwei Striche am Anfang, dann erscheint rechts ein Tipp.
        #tipp 1 1 2 gibt Tipp 2, #tipp 1 1 3 die Lösung dieser Aufgabe.
    ✅  Ganz unten steht die Prüfstation. Sie zeigt, welche Aufgaben noch offen sind.

  Beim ersten Öffnen lädt der Editor die Mathematik-Bibliothek Mathlib.
  Das kann ein bis zwei Minuten dauern.
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
elab "#prüfe " ids:ident* : command => do
  let some d ← daten "⟦0⟧ " | logWarning "Prüfdaten fehlen."
  let teile : List String := d.splitOn "|"
  let (soll, erfolg) := (teile.getD 0 "", teile.getD 1 "")
  if ids.toList.map (·.getId.toString) != soll.splitOn " " then
    logWarning "⚠️ Die Zeile #prüfe wurde verändert. Bitte die Datei neu öffnen."; return
  let mut offen := #[]
  for id in ids do
    if (← getEnv).find? id.getId |>.isNone then offen := offen.push s!"{id.getId} (fehlt)"
    else if (← Lean.collectAxioms id.getId).contains ``sorryAx then offen := offen.push s!"{id.getId}"
  if offen.isEmpty then
    logInfo m!"✅ {erfolg}"
    if let some url := teile[2]? then
      let props := Json.mkObj [("url", toJson url), ("text", toJson "▶ Hier klicken: weiter zur nächsten Mission")]
      logInfo (.ofWidget { id := ``linkWidget, javascriptHash := linkWidget.javascriptHash, props := pure props } m!"{url}")
  else logWarning m!"⏳ Noch nicht alles bewiesen.\nNoch offen: {", ".intercalate offen.toList}"

/- ═════════════════════════════════════════════════════════════
   🏁 START: Hier geht es los!
   ═════════════════════════════════════════════════════════════ -/

/- ─────────────────────────────────────────────────────────────
  Werkzeugkasten: gerade und ungerade Zahlen
──────────────────────────────────────────────────────────────── -/
/-
  Wir arbeiten mit natürlichen Zahlen ℕ = {0, 1, 2, ...}.
  Eine Zahl n ist gerade, wenn es ein k gibt mit n = 2k, und ungerade, wenn n = 2k + 1.
  "Es gibt ein k" schreibt man in Lean als ∃ k.
-/
def gerade (n : ℕ) : Prop := ∃ k, n = 2 * k
def ungerade (n : ℕ) : Prop := ∃ k, n = 2 * k + 1

-- Drei Hilfssätze, die Sie später benutzen dürfen (die Beweise müssen Sie nicht verstehen):
theorem gerade_oder_ungerade (n : ℕ) : gerade n ∨ ungerade n := by
  rcases Nat.even_or_odd' n with ⟨k, h | h⟩
  · exact Or.inl ⟨k, h⟩
  · exact Or.inr ⟨k, h⟩
theorem nicht_beides (n : ℕ) : gerade n → ¬ ungerade n := by
  rintro ⟨k, hk⟩ ⟨j, hj⟩
  omega
theorem gerade_von_nicht_ungerade {n : ℕ} (h : ¬ ungerade n) : gerade n :=
  (gerade_oder_ungerade n).resolve_right h

/- ═════════════════════════════════════════════════════════════
   1. Direkter Beweis
   ═════════════════════════════════════════════════════════════
  Muster: Sei F erfüllt. ... Also gilt G.
  In Lean:
    intro h               "Sei F erfüllt": die Voraussetzung bekommt den Namen h
    obtain ⟨k, hk⟩ := h   h sagt "es gibt ein k mit ...": k und die Gleichung hk herausholen
    exact ⟨w, by omega⟩   Behauptung "es gibt ein k": Zeuge w angeben, den Rest nachrechnen
  Zum Nachrechnen:  omega  kann lineare Rechnungen (+, Zahl · x),
                    ring   kann Polynome (x², x·y, ...), nach  subst hk  (n durch 2k+1 ersetzen).
-/

-- Beispiel (Folie "Direkter Beweis"): Ist n durch 10 teilbar, dann ist n gerade.
theorem zehn_gerade (n : ℕ) : 10 ∣ n → gerade n := by
  intro h                  -- Sei n durch 10 teilbar.
  obtain ⟨k, hk⟩ := h      -- Dann gibt es k mit n = 10 * k.
  exact ⟨5 * k, by omega⟩  -- Also n = 2 * (5k), d.h. n ist gerade.

-- ✏️ Aufgabe 1.1: Sind a und b gerade, dann ist a + b gerade.
theorem summe_gerade (a b : ℕ) : gerade a → gerade b → gerade (a + b) := by
  sorry
-- #tipp 1 1

-- Beispiel: Ist n gerade, dann ist n² gerade. Hier braucht man ring statt omega.
theorem quadrat_gerade (n : ℕ) : gerade n → gerade (n ^ 2) := by
  intro h
  obtain ⟨k, hk⟩ := h       -- n = 2k
  exact ⟨2 * k ^ 2, by subst hk; ring⟩   -- n² = 4k² = 2 · (2k²)

-- ✏️ Aufgabe 1.2 (Folie "Beispielaufgabe"): Ist n ungerade, dann ist n² + n gerade.
theorem quadrat_plus_gerade (n : ℕ) : ungerade n → gerade (n ^ 2 + n) := by
  sorry
-- #tipp 1 2

/- ═════════════════════════════════════════════════════════════
   2. Kontraposition
   ═════════════════════════════════════════════════════════════
  Statt F ⟹ G zeigt man ¬G ⟹ ¬F.
  In Lean:  contrapose! h  dreht die Aussage um: Aus der Voraussetzung h : F und
  dem Ziel G werden die Voraussetzung h : ¬G und das Ziel ¬F.
-/

-- Beispiel (Folie "Kontraposition"): Ist n² ungerade, dann ist n ungerade.
theorem quadrat_ungerade (n : ℕ) : ungerade (n ^ 2) → ungerade n := by
  intro h
  contrapose! h                                    -- jetzt: h : ¬ ungerade n, Ziel: ¬ ungerade (n²)
  obtain ⟨k, hk⟩ := gerade_von_nicht_ungerade h   -- n ist nicht ungerade, also gerade: n = 2k
  exact nicht_beides (n ^ 2) ⟨2 * k ^ 2, by subst hk; ring⟩   -- n² ist gerade, also nicht ungerade

-- ✏️ Aufgabe 2.1: Ist n³ ungerade, dann ist n ungerade.
theorem kubik_ungerade (n : ℕ) : ungerade (n ^ 3) → ungerade n := by
  sorry
-- #tipp 2 1

-- ✏️ Aufgabe 2.2 (Quiz 2 der Folien): Ist n · m nicht durch 3 teilbar, dann ist n nicht durch 3 teilbar.
theorem nicht_drei (n m : ℕ) : ¬ 3 ∣ n * m → ¬ 3 ∣ n := by
  sorry
-- #tipp 2 2

/- ═════════════════════════════════════════════════════════════
   3. Beweis durch Widerspruch
   ═════════════════════════════════════════════════════════════
  Man nimmt an, die Behauptung wäre falsch, und leitet einen Widerspruch her.
  In Lean ist ¬A dasselbe wie "aus A folgt etwas Falsches".
    intro h      Annahme A (das Gegenteil der Behauptung ¬A)
    omega        findet den Widerspruch in Rechnungen
-/

-- Beispiel: Es gibt keine größte natürliche Zahl.
theorem keine_groesste : ¬ ∃ n : ℕ, ∀ m : ℕ, m ≤ n := by
  intro h                  -- Angenommen, es gibt ein größtes n.
  obtain ⟨n, hn⟩ := h      -- Für alle m gilt m ≤ n.
  have h1 := hn (n + 1)    -- Dann auch n + 1 ≤ n.
  omega                    -- Widerspruch!

-- ✏️ Aufgabe 3.1: Es gibt keine natürliche Zahl, die kleiner als alle natürlichen Zahlen ist.
theorem keine_kleiner_als_alle : ¬ ∃ n : ℕ, ∀ m : ℕ, n < m := by
  sorry
-- #tipp 3 1

/-
  Der berühmteste Widerspruchsbeweis: √2 ist irrational (Folie "Beispiel").
  Mathlib kennt den Satz schon:
-/
theorem wurzel_zwei : Irrational (Real.sqrt 2) := irrational_sqrt_two

/-
  Der Kern des Beweises auf der Folie: Aus p² = 2q² folgt, dass 2 ein Teiler von p ist.
  Dafür braucht man: Teilt eine Primzahl p², dann teilt sie p.
-/
-- Beispiel: Teilt 3 die Zahl p², dann teilt 3 auch p.
theorem drei_teilt (p : ℕ) (h : 3 ∣ p ^ 2) : 3 ∣ p :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_three h

-- ✏️ Aufgabe 3.2: Aus p² = 2q² folgt 2 ∣ p.
theorem zwei_teilt (p q : ℕ) (h : p ^ 2 = 2 * q ^ 2) : 2 ∣ p := by
  sorry
-- #tipp 3 2

/- ═════════════════════════════════════════════════════════════
   4. Gegenbeispiel
   ═════════════════════════════════════════════════════════════
  Eine Aussage "für alle n gilt ..." widerlegt man durch EIN Gegenbeispiel.
    intro h              angenommen, es gilt für alle n
    have h1 := h 40      dann auch für n = 40
    norm_num at h1       rechnet h1 aus und findet den Widerspruch
-/

-- Beispiel: n² + n + 41 ist nicht für alle n eine Primzahl (für n = 0, ..., 39 schon!).
theorem nicht_immer_prim : ¬ ∀ n : ℕ, Nat.Prime (n ^ 2 + n + 41) := by
  intro h
  have h1 := h 40          -- 40² + 40 + 41 = 1681 = 41 · 41
  norm_num at h1

-- ✏️ Aufgabe 4.1: Widerlegen Sie: Für alle n gilt n² < 2ⁿ.
theorem nicht_immer_kleiner : ¬ ∀ n : ℕ, n ^ 2 < 2 ^ n := by
  sorry
-- #tipp 4 1

-- ✏️ Aufgabe 4.2: Widerlegen Sie: Ist n gerade, dann ist auch n / 2 gerade.
theorem nicht_immer_halb : ¬ ∀ n : ℕ, gerade n → gerade (n / 2) := by
  sorry
-- #tipp 4 2

/- ═════════════════════════════════════════════════════════════
   5. Fallunterscheidung
   ═════════════════════════════════════════════════════════════
  Man zeigt die Behauptung in jedem Fall einzeln. Wichtig: keinen Fall vergessen.
    rcases (Fall A ∨ Fall B) with h | h    teilt den Beweis in zwei Fälle
    ·                                        leitet den Beweis eines Falls ein
-/

-- Beispiel (Folie "Fallunterscheidung"): Für jede ganze Zahl z gilt z² ≥ 0.
theorem quadrat_nichtnegativ (z : ℤ) : 0 ≤ z ^ 2 := by
  rcases le_or_gt 0 z with h | h
  · nlinarith      -- Fall z ≥ 0: Produkt zweier nichtnegativer Zahlen
  · nlinarith      -- Fall z < 0: Produkt zweier negativer Zahlen ist positiv

-- Beispiel: n · (n + 1) ist gerade. Fälle: n gerade oder n ungerade.
theorem produkt_gerade (n : ℕ) : gerade (n * (n + 1)) := by
  rcases gerade_oder_ungerade n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (2 * k + 1), by subst hk; ring⟩       -- n = 2k:     2k(2k+1) = 2 · k(2k+1)
  · exact ⟨(2 * k + 1) * (k + 1), by subst hk; ring⟩ -- n = 2k + 1: (2k+1)(2k+2) = 2 · (2k+1)(k+1)

-- ✏️ Aufgabe 5.1: n² + 3n ist gerade.
theorem quadrat_plus_drei (n : ℕ) : gerade (n ^ 2 + 3 * n) := by
  rcases gerade_oder_ungerade n with ⟨k, hk⟩ | ⟨k, hk⟩
  · sorry
  · sorry
-- #tipp 5 1

/- ═════════════════════════════════════════════════════════════
   6. Äquivalenzen
   ═════════════════════════════════════════════════════════════
  F ⟺ G zeigt man in zwei Richtungen: F ⟹ G und G ⟹ F.
    constructor     teilt das Ziel F ↔ G in die zwei Richtungen
    n % 2           Rest bei Division durch 2
-/

-- Beispiel: n ist genau dann gerade, wenn n bei Division durch 2 den Rest 0 lässt.
theorem gerade_iff (n : ℕ) : gerade n ↔ n % 2 = 0 := by
  constructor
  · intro h                       -- Richtung ⟹
    obtain ⟨k, hk⟩ := h
    omega
  · intro h                       -- Richtung ⟸
    exact ⟨n / 2, by omega⟩

-- ✏️ Aufgabe 6.1: n ist genau dann ungerade, wenn n bei Division durch 2 den Rest 1 lässt.
theorem ungerade_iff (n : ℕ) : ungerade n ↔ n % 2 = 1 := by
  sorry
-- #tipp 6 1

-- ✏️ Aufgabe 6.2: n ist genau dann gerade, wenn n + 2 gerade ist.
theorem gerade_plus_zwei (n : ℕ) : gerade n ↔ gerade (n + 2) := by
  sorry
-- #tipp 6 2

/- ═════════════════════════════════════════════════════════════
   7. Vollständige Induktion
   ═════════════════════════════════════════════════════════════
  Man zeigt den Induktionsanfang (n = 0) und den Induktionsschritt
  (gilt die Aussage für n, dann auch für n + 1).
    induction n with
    | zero => ...            Induktionsanfang
    | succ n ih => ...       Induktionsschritt, ih ist die Induktionshypothese
  ∑ i ∈ Finset.range (n + 1), f i   ist die Summe f 0 + f 1 + ... + f n.
  Finset.sum_range_succ  spaltet den letzten Summanden ab.
-/

-- Beispiel: die Gaußsche Summenformel, 2 · (0 + 1 + ... + n) = n · (n + 1).
theorem gauss (n : ℕ) : 2 * (∑ i ∈ Finset.range (n + 1), i) = n * (n + 1) := by
  induction n with
  | zero => simp                               -- Induktionsanfang: 2 · 0 = 0 · 1
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]    -- letzten Summanden abspalten, ih einsetzen
    ring                                       -- n(n+1) + 2(n+1) = (n+1)(n+2)

-- ✏️ Aufgabe 7.1: Die Summe der ersten n ungeraden Zahlen ist n², also 1 + 3 + ... + (2n − 1) = n².
theorem ungerade_summe (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  sorry
-- #tipp 7 1

-- ✏️ Aufgabe 7.2: Für alle n gilt 2ⁿ ≥ n + 1.
theorem zweihoch (n : ℕ) : 2 ^ n ≥ n + 1 := by
  sorry
-- #tipp 7 2

-- ✅ PRÜFSTATION: Klicken Sie auf die nächste Zeile. Rechts steht, was noch offen ist.
#prüfe summe_gerade quadrat_plus_gerade kubik_ungerade nicht_drei keine_kleiner_als_alle zwei_teilt nicht_immer_kleiner nicht_immer_halb quadrat_plus_drei ungerade_iff gerade_plus_zwei ungerade_summe zweihoch



/- Daten für Tipps und Prüfstation (verschlüsselt, bitte nicht ändern)
⟦0⟧ tvnnf`hfsbef!rvbesbu`qmvt`hfsbef!lvcjl`vohfsbef!ojdiu`esfj!lfjof`lmfjofs`bmt`bmmf!{xfj`ufjmu!ojdiu`jnnfs`lmfjofs!ojdiu`jnnfs`ibmc!rvbesbu`qmvt`esfj!vohfsbef`jgg!hfsbef`qmvt`{xfj!vohfsbef`tvnnf!{xfjipdi}Bmmft!cfxjftfo"!Tjf!cfifsstdifo!kfu{u!bmmf!Cfxfjtnfuipefo!bvt!efn!Lbqjufm/!🎊
⟦1 1 1⟧ 💢!Bvghbcf!2/2-!Ujqq!2;![xfj!Wpsbvttfu{vohfo;!jousp!ib!ic/!Eboo!cfjef!nju!pcubjo!bvtqbdlfo-!xjf!jn!Cfjtqjfm/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!2!2!3
⟦1 1 2⟧ 💢!Bvghbcf!2/2-!Ujqq!3;!Nju!b!>!3y!voe!c!>!3z!jtu!b!,!c!>!3)y!,!z*/!Mfu{uf![fjmf;!fybdu!⟩y!,!z-!cz!pnfhb⟪¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!2!2!4
⟦1 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!2/2;¶¶uifpsfn!tvnnf`hfsbef!)b!c!;!№*!;!hfsbef!b!↓!hfsbef!c!↓!hfsbef!)b!,!c*!;>!cz¶!!jousp!ib!ic¶!!pcubjo!⟩y-!iy⟪!;>!ib¶!!pcubjo!⟩z-!iz⟪!;>!ic¶!!fybdu!⟩y!,!z-!cz!pnfhb⟪
⟦1 2 1⟧ 💢!Bvghbcf!2/3-!Ujqq!2;!Bvgcbv!xjf!jn!Cfjtqjfm!ebwps/!Sfdiofo!Tjf!bvg!Qbqjfs!bvt-!xbt!)3l,2*³!,!)3l,2*!jtu/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!2!3!3
⟦1 2 2⟧ 💢!Bvghbcf!2/3-!Ujqq!3;!)3l,2*³!,!)3l,2*!>!5l³!,!7l!,!3!>!3!¸!)3l³!,!4l!,!2*/!Mfu{uf![fjmf;!fybdu!⟩3!+!l!_!3!,!4!+!l!,!2-!cz!tvctu!il<!sjoh⟪¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!2!3!4
⟦1 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!2/3;¶¶uifpsfn!rvbesbu`qmvt`hfsbef!)o!;!№*!;!vohfsbef!o!↓!hfsbef!)o!_!3!,!o*!;>!cz¶!!jousp!i¶!!pcubjo!⟩l-!il⟪!;>!i¶!!fybdu!⟩3!+!l!_!3!,!4!+!l!,!2-!cz!tvctu!il<!sjoh⟪
⟦2 1 1⟧ 💢!Bvghbcf!3/2-!Ujqq!2;!Gbtu!hfobv!xjf!ebt!Cfjtqjfm/!Ovs!efs![fvhf!jo!efs!mfu{ufo![fjmf!åoefsu!tjdi/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!2!3
⟦2 1 2⟧ 💢!Bvghbcf!3/2-!Ujqq!3;!)3l*´!>!9l´!>!3!¸!)5l´*/!Mfu{uf![fjmf;!fybdu!ojdiu`cfjeft!)o!_!4*!⟩5!+!l!_!4-!cz!tvctu!il<!sjoh⟪¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!2!4
⟦2 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!3/2;¶¶uifpsfn!lvcjl`vohfsbef!)o!;!№*!;!vohfsbef!)o!_!4*!↓!vohfsbef!o!;>!cz¶!!jousp!i¶!!dpousbqptf"!i¶!!pcubjo!⟩l-!il⟪!;>!hfsbef`wpo`ojdiu`vohfsbef!i¶!!fybdu!ojdiu`cfjeft!)o!_!4*!⟩5!+!l!_!4-!cz!tvctu!il<!sjoh⟪
⟦2 2 1⟧ 💢!Bvghbcf!3/3-!Ujqq!2;!Xjfefs!jousp!i!voe!dpousbqptf"!i/!Ebobdi!jtu!i!;!4!∤!o-!voe!{v!{fjhfo!jtu!4!∤!o!+!n/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!3!3
⟦2 2 2⟧ 💢!Bvghbcf!3/3-!Ujqq!3;!Ufjmu!4!ejf![bim!o-!eboo!bvdi!kfeft!Wjfmgbdif!o!+!n/!Jo!Nbuimjc!ifjàu!ebt!Ewe/ewe/nvm`sjhiu!i!n-!bmtp;!fybdu!Ewe/ewe/nvm`sjhiu!i!n¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!3!3!4
⟦2 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!3/3;¶¶uifpsfn!ojdiu`esfj!)o!n!;!№*!;!­!4!∤!o!+!n!↓!­!4!∤!o!;>!cz¶!!jousp!i¶!!dpousbqptf"!i¶!!fybdu!Ewe/ewe/nvm`sjhiu!i!n
⟦3 1 1⟧ 💢!Bvghbcf!4/2-!Ujqq!2;!Bvgcbv!xjf!jn!Cfjtqjfm/!Gýs!xfmdift!n!jtu!o!=!n!tjdifs!gbmtdi@¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!2!3
⟦3 1 2⟧ 💢!Bvghbcf!4/2-!Ujqq!3;!Ofinfo!Tjf!n!>!o;!ibwf!i2!;>!io!o-!eboo!pnfhb/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!2!4
⟦3 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!4/2;¶¶uifpsfn!lfjof`lmfjofs`bmt`bmmf!;!­!∄!o!;!№-!∁!n!;!№-!o!=!n!;>!cz¶!!jousp!i¶!!pcubjo!⟩o-!io⟪!;>!i¶!!ibwf!i2!;>!io!o¶!!pnfhb
⟦3 2 1⟧ 💢!Bvghbcf!4/3-!Ujqq!2;![fjhfo!Tjf!{vfstu!3!∤!q³!nju!!ibwf!i3!;!3!∤!q!_!3!;>!⟩r!_!3-!i⟪!!)Ufjmfs!ifjàu;!q³!>!3!¸!r³*/!Eboo!xjf!jn!Cfjtqjfm/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!3!3
⟦3 2 2⟧ 💢!Bvghbcf!4/3-!Ujqq!3;![xfjuf![fjmf;!fybdu!Obu/Qsjnf/ewe`pg`ewe`qpx!Obu/qsjnf`uxp!i3¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!4!3!4
⟦3 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!4/3;¶¶uifpsfn!{xfj`ufjmu!)q!r!;!№*!)i!;!q!_!3!>!3!+!r!_!3*!;!3!∤!q!;>!cz¶!!ibwf!i3!;!3!∤!q!_!3!;>!⟩r!_!3-!i⟪¶!!fybdu!Obu/Qsjnf/ewe`pg`ewe`qpx!Obu/qsjnf`uxp!i3
⟦4 1 1⟧ 💢!Bvghbcf!5/2-!Ujqq!2;!Qspcjfsfo!Tjf!lmfjof![bimfo!bvt;!o!>!1-!2-!3-!4-!///!Gýs!xfmdift!o!tujnnu!ft!ojdiu@¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!2!3
⟦4 1 2⟧ 💢!Bvghbcf!5/2-!Ujqq!3;!Gýs!o!>!3!jtu!5!=!5!gbmtdi;!jousp!i-!eboo!ibwf!i2!;>!i!3-!eboo!opsn`ovn!bu!i2¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!2!4
⟦4 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!5/2;¶¶uifpsfn!ojdiu`jnnfs`lmfjofs!;!­!∁!o!;!№-!o!_!3!=!3!_!o!;>!cz¶!!jousp!i¶!!ibwf!i2!;>!i!3¶!!opsn`ovn!bu!i2
⟦4 2 1⟧ 💢!Bvghbcf!5/3-!Ujqq!2;!Hfhfocfjtqjfm!o!>!3;!3!jtu!hfsbef!)[fvhf!2*-!bcfs!3!0!3!>!2!ojdiu/!i!3!csbvdiu!eftibmc!opdi!efo!Cfxfjt!⟩2-!sgm⟪-!ebtt!3!hfsbef!jtu/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!3!3
⟦4 2 2⟧ 💢!Bvghbcf!5/3-!Ujqq!3;!jousp!i-!eboo!pcubjo!⟩l-!il⟪!;>!i!3!⟩2-!sgm⟪!)il!tbhu!3!0!3!>!3l*-!eboo!pnfhb¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!5!3!4
⟦4 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!5/3;¶¶uifpsfn!ojdiu`jnnfs`ibmc!;!­!∁!o!;!№-!hfsbef!o!↓!hfsbef!)o!0!3*!;>!cz¶!!jousp!i¶!!pcubjo!⟩l-!il⟪!;>!i!3!⟩2-!sgm⟪¶!!pnfhb
⟦5 1 1⟧ 💢!Bvghbcf!6/2-!Ujqq!2;!Ejf!Gbmmvoufstdifjevoh!tufiu!tdipo!eb/!Sfdiofo!Tjf!jo!kfefn!Gbmm!bvg!Qbqjfs!)3l*³!,!4¸3l!c{x/!)3l,2*³!,!4)3l,2*!bvt/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!6!2!3
⟦5 1 2⟧ 💢!Bvghbcf!6/2-!Ujqq!3;!Gbmm!2;!5l³!,!7l!>!3)3l³!,!4l*/!Gbmm!3;!5l³!,!21l!,!5!>!3)3l³!,!6l!,!3*/!Kf;!fybdu!⟩[fvhf-!cz!tvctu!il<!sjoh⟪¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!6!2!4
⟦5 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!6/2;¶¶uifpsfn!rvbesbu`qmvt`esfj!)o!;!№*!;!hfsbef!)o!_!3!,!4!+!o*!;>!cz¶!!sdbtft!hfsbef`pefs`vohfsbef!o!xjui!⟩l-!il⟪!}!⟩l-!il⟪¶!!¸!fybdu!⟩3!+!l!_!3!,!4!+!l-!cz!tvctu!il<!sjoh⟪¶!!¸!fybdu!⟩3!+!l!_!3!,!6!+!l!,!3-!cz!tvctu!il<!sjoh⟪
⟦6 1 1⟧ 💢!Bvghbcf!7/2-!Ujqq!2;!Hfobv!xjf!jn!Cfjtqjfm-!ovs!nju!Sftu!2/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!7!2!3
⟦6 1 2⟧ 💢!Bvghbcf!7/2-!Ujqq!3;!dpotusvdups-!eboo!{xfj!Sjdiuvohfo!xjf!jn!Cfjtqjfm/!Efs![fvhf!jo!efs!Sýdlsjdiuvoh!jtu!xjfefs!o!0!3/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!7!2!4
⟦6 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!7/2;¶¶uifpsfn!vohfsbef`jgg!)o!;!№*!;!vohfsbef!o!↕!o!&!3!>!2!;>!cz¶!!dpotusvdups¶!!¸!jousp!i¶!!!!pcubjo!⟩l-!il⟪!;>!i¶!!!!pnfhb¶!!¸!jousp!i¶!!!!fybdu!⟩o!0!3-!cz!pnfhb⟪
⟦6 2 1⟧ 💢!Bvghbcf!7/3-!Ujqq!2;!dpotusvdups-!eboo!jo!cfjefo!Sjdiuvohfo;!jousp!i-!pcubjo!⟩l-!il⟪!;>!i!voe!fjofo![fvhfo!bohfcfo/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!7!3!3
⟦6 2 2⟧ 💢!Bvghbcf!7/3-!Ujqq!3;!Ijosjdiuvoh;!o!,!3!>!3)l!,!2*-![fvhf!l!,!2/!Sýdlsjdiuvoh;!o!>!3)l!.!2*-![fvhf!l!.!2/!Kfxfjmt!cz!pnfhb/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!7!3!4
⟦6 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!7/3;¶¶uifpsfn!hfsbef`qmvt`{xfj!)o!;!№*!;!hfsbef!o!↕!hfsbef!)o!,!3*!;>!cz¶!!dpotusvdups¶!!¸!jousp!i¶!!!!pcubjo!⟩l-!il⟪!;>!i¶!!!!fybdu!⟩l!,!2-!cz!pnfhb⟪¶!!¸!jousp!i¶!!!!pcubjo!⟩l-!il⟪!;>!i¶!!!!fybdu!⟩l!.!2-!cz!pnfhb⟪
⟦7 1 1⟧ 💢!Bvghbcf!8/2-!Ujqq!2;!Bvgcbv!xjf!cfj!hbvtt;!joevdujpo!o!xjui-!Gbmm!{fsp!nju!tjnq-!jn!Gbmm!tvdd!{vfstu!sx!\Gjotfu/tvn`sbohf`tvdd-!ji^/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!8!2!3
⟦7 1 2⟧ 💢!Bvghbcf!8/2-!Ujqq!3;!Gbmm!tvdd;!sx!\Gjotfu/tvn`sbohf`tvdd-!ji^!voe!ebobdi!sjoh/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!8!2!4
⟦7 1 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!8/2;¶¶uifpsfn!vohfsbef`tvnnf!)o!;!№*!;!−!j!∉!Gjotfu/sbohf!o-!)3!+!j!,!2*!>!o!_!3!;>!cz¶!!joevdujpo!o!xjui¶!!}!{fsp!>?!tjnq¶!!}!tvdd!o!ji!>?¶!!!!sx!\Gjotfu/tvn`sbohf`tvdd-!ji^¶!!!!sjoh
⟦7 2 1⟧ 💢!Bvghbcf!8/3-!Ujqq!2;!Joevlujpo!xjf!fcfo/!Jn!Tdisjuu!ijmgu!sx!\qpx`tvdd^;!Ft!tdisfjcu!3_)o,2*!bmt!3_o!¸!3/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!8!3!3
⟦7 2 2⟧ 💢!Bvghbcf!8/3-!Ujqq!3;!Gbmm!tvdd;!sx!\qpx`tvdd^-!ebobdi!pnfhb!)ft!cfovu{u!ejf!Joevlujpotizqpuiftf!ji!;!3_o!≦!o!,!2*/¶¶Opdi!fjo!Tdisjuu!xfjufs;!$ujqq!8!3!4
⟦7 2 3⟧ 🔒!M÷tvoh!{v!Bvghbcf!8/3;¶¶uifpsfn!{xfjipdi!)o!;!№*!;!3!_!o!≦!o!,!2!;>!cz¶!!joevdujpo!o!xjui¶!!}!{fsp!>?!tjnq¶!!}!tvdd!o!ji!>?¶!!!!sx!\qpx`tvdd^¶!!!!pnfhb
-/
