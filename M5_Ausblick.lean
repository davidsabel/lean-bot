import Mathlib
/-
  Mission 5: Ausblick, die große Bibliothek Mathlib
  =================================================
  Hängst du fest? Unter jeder Aufgabe steht eine Zeile wie  -- #tipp 5 1
  Lösche die zwei Striche am Anfang: Rechts erscheint Tipp 1.
  Mit  #tipp 5 1 2  kommt Tipp 2, mit  #tipp 5 1 3  die Lösung dieser Aufgabe.

  Mathlib ist eine riesige Sammlung formal bewiesener Mathematik
  (über 250 000 Sätze), geschrieben von Hunderten Freiwilligen.
  Alles darin hat Lean geprüft. Du kannst die Sätze benutzen wie Bibliotheksfunktionen.
-/

/- ⚙️ Tipp-Werkzeug (bitte nicht ändern). Weiter unten geht es los! -/
def tippText (hex : List Char) : String := Id.run do
  let k := "DDA-2026".toList.map Char.toNat
  let w (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
  let mut b : ByteArray := .empty
  for i in [0:hex.length / 2] do
    b := b.push ((w hex[2*i]! * 16 + w hex[2*i+1]!) ^^^ k[i % k.length]!).toUInt8
  return (String.fromUTF8? b).getD "?"
open Lean Elab Command in
elab "#tipp " m:num a:num s:(num)? : command => do
  let (x, y, z) := (m.getNat, a.getNat, (s.map (·.getNat)).getD 1)
  let marke := s!"⟦{x} {y} {z}⟧ ".toList
  let zeilen := ((← getFileMap).source.splitOn "\n").map (·.toList.dropWhile (· == ' '))
  match zeilen.find? (marke.isPrefixOf ·) with
  | none => logWarning m!"Zu Aufgabe {x}.{y} gibt es keinen Tipp {z}."
  | some zeile =>
    let text := tippText ((zeile.drop marke.length).filter (·.isAlphanum))
    if z == 3 then logInfo m!"🔑 Lösung zu Aufgabe {x}.{y}:\n\n{text}"
    else logInfo m!"💡 Aufgabe {x}.{y}, Tipp {z}: {text}\n\nNoch ein Schritt weiter: #tipp {x} {y} {z + 1}"

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
  ⟦5 1 1⟧ 1727294c4710565f366423485b43425f21281e186d0112572a7e61695d4246163e21284a4610575f2a2161485b5e485f23216179535b465f2f686149534341167574700d57595c53641433445f4a535e2864285e461e
  ⟦5 1 2⟧ 2a2b33406d5e475b
  ⟦5 1 3⟧ 302c244240555f162621285e4259575a1b711e1e120a127825306f7d40595f53646c730d6c10051669647004120a0f16263d4b0d125e5d44291b2f585f
-/
#mission 5 prüft beispiel_5_3
