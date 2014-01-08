%.out: %.cpp
	g++ -o /tmp/tmp_exec_test $^ && /tmp/tmp_exec_test > $@ && rm /tmp/tmp_exec_test


%: %.cpp
	g++ -o $@ $^
	./$@
	./$@ > $*.out

