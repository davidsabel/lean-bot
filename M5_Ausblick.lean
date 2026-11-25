import Mathlib
/-
  Mission 5: Ausblick, die große Bibliothek Mathlib
  =================================================
  Hängst du fest? Hier ist dieselbe Mission mit Tipps (Strg+Klick):
  https://live.lean-lang.org/#url=https%3A%2F%2Fgist.githubusercontent.com%2Fdavidsabel%2F12dc468ede87291e5ad712797f23ed1a%2Fraw%2FM5_Ausblick_Tipps.lean

  Mathlib ist eine riesige Sammlung formal bewiesener Mathematik
  (über 250 000 Sätze), geschrieben von Hunderten Freiwilligen.
  Alles darin hat Lean geprüft. Du kannst die Sätze benutzen wie Bibliotheksfunktionen.
-/

-- Was sagt ein Satz? #check zeigt die Aussage (den Typ):
#check Nat.exists_infinite_primes   -- Euklid: Über jeder Zahl liegt eine Primzahl

-- Mathlib-Taktiken rechnen für uns:
-- 👀 VORMACHEN
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

-- ✍️ NACHMACHEN (Aufgabe 5.1): 2^7 - 1 = 127 ist eine Primzahl (eine Mersenne-Primzahl).
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


#mission 5 prüft beispiel_5_3
