
# we define this variable in order to be set from the caller
# program if a different input file name is desired
input='hol-loading-output-redirection.txt' 

theorems-quick-reference:
	gawk -f theorems-quick-reference-maker.awk ${input} > theorems-quick-reference.txt

conversions-quick-reference:
	gawk -f conversions-quick-reference-maker.awk ${input} > conversions-quick-reference.txt

conversionals-quick-reference:
	gawk -f conversionals-quick-reference-maker.awk ${input} > conversionals-quick-reference.txt

tactics-quick-reference:
	gawk -f tactics-quick-reference-maker.awk ${input} > tactics-quick-reference.txt

thm-tactics-quick-reference:
	gawk -f thm-tactics-quick-reference-maker.awk ${input} > thm-tactics-quick-reference.txt

all: theorems-quick-reference conversions-quick-reference conversionals-quick-reference tactics-quick-reference thm-tactics-quick-reference
	gawk -f thm-tactics-quick-reference-maker.awk ${input} > thm-tactics-quick-reference.txt
	cat theorems-quick-reference.txt conversions-quick-reference.txt conversionals-quick-reference.txt tactics-quick-reference.txt thm-tactics-quick-reference.txt > comprehensive-quick-reference.txt

clean-quick-references:
	rm -f theorems-quick-reference.txt
	rm -f conversions-quick-reference.txt
	rm -f conversionals-quick-reference.txt
	rm -f tactics-quick-reference.txt
	rm -f thm-tactics-quick-reference.txt 
	rm -f comprehensive-quick-reference.txt
