#!/usr/bin/sed -f
/\/\*@/,/\*\//{
	s/>=/≥/g
	s/\\in/∈/g
	s/!=/≢/g
	s/<==>/⇔/g
	s/<=/≤/g
	s/==>/⇒/g
	s/==/≡/g
	s/&&/∧/g
	s/||/∨/g
	s/^^/⊻/g
	s/!/¬/g
	s/\\forall/∀/g
	s/\\exists/∃/g
	s/\binteger\b/ℤ/g
	s/\breal\b/ℝ/g
	s/\bboolean\b/𝔹/g
	s/\\pi/π/g
}
