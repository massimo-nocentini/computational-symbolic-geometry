#/val \w+ : thm =/ && next ~ /val \w+ : thm =/ { print }

#$0 ~ /^val \w+ : thm =$/ , $0 ~ /^val \w+ : thm =/  { #print "hello" if ($0 ~ /^\s+/ ) print "Hello"; #if ($0 ~ /^val \w+ : thm =/) previous ; }

# the following doesn't print any "Hello" since the range is exhausted by the very same 
# line that starts with "val..." and is a `theorem`-line, moreover the if condition
# cannot be satisfied by this `theorem`-line .
#$0 ~ /^val \w+ : thm =$/ , $0 ~ /^val \w+ : thm =/  { if ($0 ~ /^\s+/ ) print "Hello" }

# working
#/^val \w+ : thm =/ { print }

#$0 ~ /^\s+/ { print }

# the following line is necessary to filter the `header` line
# about OCaml P4 precessor.
#/Camlp5/ { next }

/^val \w+'* : (conv|term -> thm) = / {  print }

