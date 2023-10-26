#/bin/bash

gambit mutate --json gambit_conf.json

cd certora

for i in $(find ./mutations/gambit/mutants -name '*.sol');
do
#    mv -v $i $dest
  if [[ $i == *RoleStore.sol ]]
  then
    cp $i ../contracts/role
  elif [[ $i == *DataStore.sol ]]
  then
    cp $i ../contracts/data
  elif [[ $i == *Bank.sol ]]
  then
    cp $i ../contracts/bank
  elif [[ $i == *OracleStore.sol ]]
  then
    cp $i ../contracts/oracle
  elif [[ $i == *Oracle.sol ]]
  then
    cp $i ../contracts/oracle
  else
	  echo $i
    exit 0
  fi

	make bug
	make restore
done;

cd ..

for f in certora/mutations/participants/*.patch
do
    echo "Applying $f"
    git apply $f
    echo "Running jobs"
    for conf in certora/confs/*_verified.conf
    do
		echo "Running $conf"
		certoraRun $conf --msg "$conf $f"
	done
    echo "Reverting $f"
    git apply -R $f
done
