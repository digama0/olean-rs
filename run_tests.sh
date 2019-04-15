#! /bin/sh
lean --make test/simple.lean
lean --make test/simple2.lean
echo "* test -D"
cargo run -- -D test/simple.olean | tail -n +2 > test/simple.lean.actual
diff test/simple.lean.actual test/simple.lean.expected || exit -1

cd test
leanpkg configure
echo "* test -d"
cargo run -- -d simple | tail -n +2 > leanpkg.actual
diff leanpkg.actual leanpkg.expected || exit -1

echo "* test -u"
cargo run -- -u simple2 | tail -n +2 > unused.actual
diff unused.actual unused.expected || exit -1
