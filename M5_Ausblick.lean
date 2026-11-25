import Mathlib
/-
  Mission 5: Ausblick, die große Bibliothek Mathlib
  =================================================
  Hängst du fest? Schreibe ganz unten in eine neue Zeile zum Beispiel
      #tipp 5 1        (Tipp 1 zu Aufgabe 5.1)
      #tipp 5 1 2      (Tipp 2)
      #tipp 5 1 3      (Lösung dieser Aufgabe)
  und klicke darauf. Rechts erscheint die Hilfe.

  Mathlib ist eine riesige Sammlung formal bewiesener Mathematik
  (über 250 000 Sätze), geschrieben von Hunderten Freiwilligen.
  Alles darin hat Lean geprüft. Du kannst die Sätze benutzen wie Bibliotheksfunktionen.
-/

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


/-
  ═════════════════════════════════════════════════════════════
  PRÜFSTATION der Discrete Droid Academy. Bitte nicht ändern!
  Klicke auf die letzte Zeile (#mission). Rechts steht dann,
  ob die Mission geschafft ist, und dein Code für ILIAS.
  ═════════════════════════════════════════════════════════════
-/
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


/-- Hilfen: `#tipp m a` zeigt Tipp 1 zu Aufgabe m.a, `#tipp m a 2` Tipp 2, `#tipp m a 3` die Lösung. -/
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
    (5, 1, 1, "1727294c4710565f366423485b43425f21281e186d0112572a7e61695d4246163e21284a4610575f2a2161485b5e485f23216179535b465f2f686149534341167574700d57595c53641433445f4a535e2864285e461e"),
    (5, 1, 2, "2a2b33406d5e475b"),
    (5, 1, 3, "302c244240555f162621285e4259575a1b711e1e120a127825306f7d40595f53646c730d6c10051669647004120a0f16263d4b0d125e5d44291b2f585f")
  ]
  let nr := s!"{m.getNat}.{a.getNat}"
  match tabelle.find? (fun (x, y, z, _) => x == m.getNat && y == a.getNat && z == stufe) with
  | some (_, _, z, hex) =>
    if z == 3 then
      logInfo m!"🔑 Lösung zu Aufgabe {nr}:\n\n{tippText hex}"
    else
      logInfo m!"💡 Aufgabe {nr}, Tipp {z}: {tippText hex}\n\nNoch ein Schritt weiter: #tipp {m.getNat} {a.getNat} {z + 1}"
  | none => logWarning m!"Zu Aufgabe {nr} gibt es keinen Tipp {stufe}. Probiere z.B. #tipp {m.getNat} 1"

#mission 5 prüft beispiel_5_3
