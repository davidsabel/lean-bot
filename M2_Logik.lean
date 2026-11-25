import Lean
/-
  Mission 2: Beweise sind Programme
  =================================
  Hängst du fest? Unter jeder Aufgabe steht eine Zeile wie  -- #tipp 2 1
  Lösche die zwei Striche am Anfang: Rechts erscheint Tipp 1.
  Mit  #tipp 2 1 2  kommt Tipp 2, mit  #tipp 2 1 3  die Lösung dieser Aufgabe.

  In Lean ist eine Aussage ein TYP und ein Beweis ist ein WERT dieses Typs.
  Eine Aussage zu beweisen heißt also: ein Programm schreiben, das den
  passenden Typ hat. Lean prüft den Typ, genau wie ein Compiler.

  Übersetzungstabelle (Logik  ↔  Programmieren):
    A → B      Funktion, die aus einem Beweis von A einen Beweis von B macht
    A ∧ B      Paar ⟨a, b⟩ aus einem Beweis von A und einem von B
    A ∨ B      entweder links (Or.inl a) oder rechts (Or.inr b)
    ¬A         Funktion A → False ("aus A folgt Unsinn")
-/

/- ⚙️ Werkzeuge der Discrete Droid Academy: Tipps und Prüfstation (bitte nicht ändern).
   Weiter unten geht es los! -/
def tippHex (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
def tippText (hex : String) : String := Id.run do
  let k := "DDA-2026".toUTF8
  let cs := hex.toList.toArray
  let mut b : ByteArray := .empty
  for i in [0:cs.size / 2] do
    b := b.push ((tippHex cs[2*i]! * 16 + tippHex cs[2*i+1]!) ^^^ (k.get! (i % k.size)).toNat).toUInt8
  return (String.fromUTF8? b).getD "?"
open Lean Elab Command in
elab "#tipp " m:num a:num s:(num)? : command => do
  let stufe := (s.map (·.getNat)).getD 1
  let tabelle : List (Nat × Nat × Nat × String) := [
    (2, 1, 1, "03212f4c4710455f216423485b43425f21281e5745555b4221376d0d5c454016332d334912545b5337292041125453456401137e6675127736233440575e46163e3133ee8e5359512123244f575e1c"),
    (2, 1, 2, "22312f0d53106d16797a614c"),
    (2, 1, 3, "302c244240555f162531274a53525769761b700d1a711274647e617d405f421f647e616c12d2b4a4640661cfb4a21277647e7c27121054432a64200d6d100f086425"),
    (2, 2, 1, "0036244412714051312924434655081622647b0d7310d0b0d66403011257120c640661cfb4a2127564312f491251120c64056f0d655957162621280d50555b45342d24416d5d421633212f495744125b252a616b475e59422d2b2f485c1053586864254457435f5728643b5a5759125e2d2a354840555b58252a2548401e"),
    (2, 2, 2, "0531320d53105f57272c350d5410575f2a212f0d705545532d37615b5d5e12746864254c405147456429204e5a44125164212843575e127421332444411044592a640217125647586422614a1251120b7a64260d1a5612576d"),
    (2, 2, 3, "302c244240555f162531274a53525769761b730d1a7112746407611712604059346d611712187316a6c2d30d701912d4c2d661057010d0b0d664020412d2b4a4640561cfb4a21275647e7c27121054432a64270d55105316797a614a12185416256d"),
    (2, 3, 1, "1425205f1251474534252246575e12412d2161445c1050532d373144575c6d432a206d0d56515c58642a345f1254575864212843575e1262212d2d0d484540f5f8272a4a575257586a"),
    (2, 3, 2, "22312f0dd0af9a5768641ecfad99120b7a64200d1a545744643e36485b4457161021284112475b4420642f44515846162321235f5345515e306861495342475b641b68"),
    (2, 3, 3, "302c244240555f162531274a53525769761b720d1a711274647e617d405f421f647e616c12d2ba91640661cfb4a21277647e7c27121054432a64a3b29a511e161ba6de84120d0c1625"),
    (2, 4, 1, "1e3324441271405131292443465512412d2161445c1050532d373144575c6d4c3321285957431c161e3133ee8e5359512123244f575e12412d36250d57595c161425205f12475b53642d2f0d50555b45342d24416d455c526a"),
    (2, 4, 2, "22312f0d53105016797a61cfad98531a6426a3b29b"),
    (2, 4, 3, "302c244240555f162531274a53525769761b750d1a711274647e617d405f421f647e616c12d2b4a4640661cfb4a2127764a6c98a1272120c794e610d54455c162564230d0f0e12d4dbec20011252d0a9ed"),
    (2, 5, 1, "002d245e5f515e162d37350d565957161601026566751265212d3548125257412d2132485c1e"),
    (2, 5, 2, "22312f0d50100f08640b33035b5e401626"),
    (2, 5, 3, "302c244240555f162531274a53525769761b740d1a711274647e617d405f421f647e616f12d2b4a4640561cfba981274647e7c27121054432a64230d0f0e1279366a2843401050"),
    (2, 6, 1, "02252d41475e465336372245575956432a23615a5b55125f2a6423485b43425f21281e4256554018640d2f0d50555b52212a616bf1945e5a212a614553434616203161485b5e57586406245a57594116322b2f0d731e"),
    (2, 6, 2, "22312f0d5a100f08642920595158125e643328595a104e160b366f445c5c125764797f0d53104e160b366f445c42125764797f0d53101a4c3321280d68555b5a212a615a5b55125f296403485b43425f212868"),
    (2, 6, 3, "302c244240555f162531274a53525769761b770d1a71120c641433424219120c640561cfba98127764a6c7bf1271120c794e610d54455c162c647c13125d5342272c614512475b422c4e610d12104e160b366f445c5c125764797f0d533a121664643d0d7d421c5f2a36614c120d0c1625"),
    (2, 7, 1, "1727295f575950536421320d55555c5731372e0d5a595c16332d240d50555b45342d24416d5e5b552c306f0d7e555358643728485a441e162025325e125457446410385d1254574437212d4f57105b45306a"),
    (2, 7, 2, "22312f0d53105c5764797f0d5c511257"),
    (2, 7, 3, "302c244240555f162531274a53525769761b760d1a71120c641433424219120c640561cfb4a212f4e886ed6c120a0f3c646427585c1053162a2561100c105c576425"),
    (2, 8, 1, "0d296148404346532a64074c5e5c125e2537350d56451257647e616c12455c526426611712721e162d29615745555b42212a614c120a127764312f491253120c64076f0d65f3965e282161405b44125a2122350d5d5457446436284a5a4412522d21615d534341532a20240d61555b422168615a5b55125f2a6423485b43425f21281e59535b465f2f1b2e4957421c"),
    (2, 8, 2, "386428435e105016797a61415756460d6421394c514412d4dbec20011252d0a9ed64344356104e162d2a330d51100f086436284a5a440916213c204e4610d0a9ec256d0d51d2ad9f"),
    (2, 8, 3, "302c244240555f162531274a53525769761b790d1a7112746407611712604059346d6117127112d4cce361057010d0beec64020412d2b4a4646c000dd0b89516066d61cfba98121e0564a3a59510711f647e7c0d50493816642d2f59405f12d4dbec20011258d0a9ed4e610d515141533764290d4559465e4e64615112595c5a642661100c105e5322307a0d574853553064a3b29a511e1626a6de843810124a642d2f5f1253120b7a6433445558460d6421394c514412d4dbec20011253d0a9ed"),
    (2, 9, 1, "062126445c5e5716292d350d5b5e46442b64290d475e5616272b2f5e46424755302b330d455957162d2a614f575941462d212d72465159422d2f1e585c541c1600252f4312594142643e6f6f1c10f09a05643b58124a575f23212f0112515e452b6424445c551270312a2a595b5f5c0c642d2f59405f12576a"),
    (2, 9, 2, "092d350d531008160564294c4144125231640e5f1c595c5a64256117127112d4ccec616f1e1047582064290d5f51515e3064254c405147456402204141550816213c204e46105a166c0b33035b5e5e16256d6f0d74f38e446406614a575e5343372b61405b441279366a2843401e"),
    (2, 9, 3, "302c244240555f162531274a53525769761b780d1a711274647e617d405f421f647e61ef9e187316a6cce90d701912d4c2d661ef9e7112d4cce361ef9e72120c796423543810125f2a3033421258381664272e434144404327302e5f381012f4f364284346425d16257f61484a515142642c61057d421c5f2a28614c1b3a121686f361445c44405964267a0d574853553064290d1a7f40182d2a330d5019")
  ]
  let nr := s!"{m.getNat}.{a.getNat}"
  match tabelle.find? (fun (x, y, z, _) => x == m.getNat && y == a.getNat && z == stufe) with
  | some (_, _, z, hex) =>
    if z == 3 then
      logInfo m!"🔑 Lösung zu Aufgabe {nr}:\n\n{tippText hex}"
    else
      logInfo m!"💡 Aufgabe {nr}, Tipp {z}: {tippText hex}\n\nNoch ein Schritt weiter: #tipp {m.getNat} {a.getNat} {z + 1}"
  | none => logWarning m!"Zu Aufgabe {nr} gibt es keinen Tipp {stufe}. Probiere z.B. #tipp {m.getNat} 1"
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

/- ═══ PRÜFSTATION ═══ Klicke auf die nächste Zeile. Rechts steht dann, ob die Mission
   geschafft ist, und dein Code für ILIAS. Bitte die Zeile nicht ändern. -/
#mission 2 prüft aufgabe_2_1 aufgabe_2_2 aufgabe_2_3 aufgabe_2_4 aufgabe_2_5 aufgabe_2_6 aufgabe_2_7 aufgabe_2_8 aufgabe_2_9
