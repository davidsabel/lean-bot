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
    (3, 1, 1, "13212d4e5a55126c252c2d0d5b4346162021330d68554751217b6169535e5c16332d240d5b5d1274212d325d5b555e0c64a6de85685547512168615f545cd0a9ed6a"),
    (3, 1, 2, "a6dbe91c011c12442228a3b29b"),
    (3, 1, 3, "302c244240555f162531274a53525769771b700d0810d0bec7642f0d08107c5730686143121b12586479611f0410080b64a6de8503031e1636222dcfad99"),
    (3, 2, 1, "707661101202121c642f6f0d65555e552c21320d590f"),
    (3, 2, 2, "a6dbe91f031c12442228a3b29b"),
    (3, 2, 3, "302c244240555f162531274a53525769771b730d0810555336252548120400167e7961cfad9800076864334b5ed2ad9f"),
    (3, 3, 1, "132d240d5b5d1274212d325d5b555e186413244151585744641e24585555125d6421334bf18c5e5a3064730d18105c167964730d18105909"),
    (3, 3, 2, "22312f0d5c100f0864a6de855c1c12543d642e40575753d4dbed"),
    (3, 3, 3, "302c244240555f162531274a53525769771b720d0810d0bec4642f0d08107c573068614a574253522164691f121a12586d647b1038101250312a6143120d0c16a6dbe9431e10504f642b2c485551d0a9ed"),
    (3, 4, 1, "002d240d57424142212a615745555b161e212841575e12452d2a250d55555c573164364457105b5b6406244441405b53286a61634742125221366177574555536487e543565540426437284e5a1e"),
    (3, 4, 2, "0531320d5c100f1676646b0d591054592823350d5c10191676647c0d001018166c2f610612011b1864082459484457161e212841570a12533c25225912d2ad9e2f646a0d031c12543d642e40575753d4dbed"),
    (3, 4, 3, "302c244240555f162531274a53525769771b750d0810d0bec4642f0d08107c573068614a5742535221642f0dd0b6a0162321334c5655121e2a646a0d0019120c796423543810125f2a303342125e125e4e6461425044535f2a64a3b29a5b1e162c2fa3b29b10080b642c4b0d12554a57273061cfad9859166f64700112524b162b29244a53d2ad9f"),
    (3, 5, 1, "00362444126a575f28212f0d455957162d29616f575941462d212d031267575a272c240d68515a5a642d3259125453456403244a575e50532d373144575c0d"),
    (3, 5, 2, "2d2a355f5d105a1a642020435c105a5732216145030002167e796145120102066864254c5c5e12592921264c"),
    (3, 5, 3, "302c244240555f162531274a53525769771b740d0810f09a646ca3a5b2105c167e640f4c461c12586478611c02001b167e79614f4b3a12162d2a355f5d105a3c6464294c4455125e7574710d080d125e6475711d381012592921264c"),
    (3, 6, 1, "0025320d755555532a26244441405b532864285e461003186409285912595c42362b614512475b53642b23485c1050532f2b2c40414412523164290d031008162321334c565512076a64054c41105b45306424445c10625725366d0d5651411629252f0d5f5946162b26354c5b5e12573137314c515b5758642f20435c101a412d2161445c1050532d373144575c6d46283132191b1e"),
    (3, 6, 2, "2d2a355f5d105a1a642020435c105d543025284312d2ad9e2f68614559d2ad9f647e7c0d5a1003166c2c2a0d081003167964730d1810591f6864254c5c5e12592921264c"),
    (3, 6, 3, "302c244240555f162531274a53525769771b770d0810f09a646ca3a5b2105c167e640f4c461c12512136204957105c1f647e7c0d50493816642d2f59405f125e4e6461425044535f2a64a3b29a5b1e162c2fa3b29b10080b642c611c381012592921264c")
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

/- ═══ PRÜFSTATION ═══ Klicke auf die nächste Zeile. Rechts steht dann, ob die Mission
   geschafft ist, und dein Code für ILIAS. Bitte die Zeile nicht ändern. -/
#mission 3 prüft aufgabe_3_1 aufgabe_3_2 aufgabe_3_3 aufgabe_3_4 aufgabe_3_5 aufgabe_3_6
