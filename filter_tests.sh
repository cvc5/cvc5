cat test/unit/api/cpp/solver_black.cpp |grep TEST | cut -d, -f2 | sed 's/)//g' |sed 's/ //g' | tr '[:upper:]' '[:lower:]' > ~/tmp.tmp
cat test/unit/api/python/test_solver.py |grep test_  |cut -d' ' -f2 | sed 's/(solver)://g' | sed 's/test_//g' | sed 's/_//g' >> ~/tmp.tmp
cat ~/tmp.tmp | sort | uniq -c | sort -n | grep '1 ' |cut -d1 -f2- | cut -d' ' -f2- | sort


