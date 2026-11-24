while pgrep -f batch1.sh > /dev/null; do sleep 5; done
bash batch2.sh > batch2.log 2>&1
