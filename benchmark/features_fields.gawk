BEGIN { RS = "[,\n]" }
match($0, /"([^[:blank:]]+)"[[:blank:]]*:/, data) && !uniq[data[1]]++ { print data[1] }
