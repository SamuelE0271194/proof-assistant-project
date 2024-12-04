all:
	dune build

#Uncomment this once ready, you can add more tests here

manual:
	dune exec ./prover.exe

proof: 
	@read -p "Proof filename : " filename; \
	cat $$filename | dune exec ./prover.exe


