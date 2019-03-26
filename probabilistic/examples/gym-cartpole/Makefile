all: build

build:
	dune build

exec:
	dune exec ./main.exe

exec_smart:
	dune exec ./smart_main.exe

exec_pid:
	dune exec ./pid_main.exe

exec_smart_pid:
	dune exec ./smart_pid_main.exe

exec_simple_pid:
	dune exec ./simple_pid_main.exe

clean:
	dune clean
cleanall: clean
	rm -f *~
