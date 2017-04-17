all:
	compcert/clightgen csrc/*.c
	coqc -noglob -R compcert compcert -R csrc csrc csrc/*.v
	#coqc -noglob -R compcert compcert *.v
