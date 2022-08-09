#!/bin/bash    
dot -Txdot_json $1 | jq '.objects = (.objects | map(. | select(.label!=null)))' > $2
