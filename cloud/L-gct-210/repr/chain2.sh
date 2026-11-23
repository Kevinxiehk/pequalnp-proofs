while pgrep -f "batch[12].sh" > /dev/null || pgrep -f chain.sh > /dev/null; do sleep 5; done
bash batch3.sh > batch3.log 2>&1
