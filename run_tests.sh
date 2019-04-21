#! /bin/sh
cp target/release/olean-rs test/
lean --make test/simple.lean
lean --make test/simple2.lean
echo "* test -D"
olean-rs -D test/simple.olean > test/simple.lean.actual
diff test/simple.lean.actual test/simple.lean.expected || exit -1

cd test
leanpkg configure
echo "* test -d"
olean-rs -d simple.olean > leanpkg.actual
diff leanpkg.actual leanpkg.expected || exit -1

echo "* test -u"
olean-rs -u simple2.olean > unused.actual
diff unused.actual unused.expected || exit -1
