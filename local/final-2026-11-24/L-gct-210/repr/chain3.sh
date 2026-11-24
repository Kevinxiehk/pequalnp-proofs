while pgrep -f "batch[123].sh" > /dev/null || pgrep -f "chain2?.sh" > /dev/null; do sleep 5; done
bash batch5.sh > batch5.log 2>&1
