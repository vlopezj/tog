BEGIN { OFS = "" }
function field_str(name, value) {
    field_lit(name, sprintf("\"%s\"", value))
}

function field_lit(name, value) {
    printf "%s\"%s\": %s", delimiter, name, value
    delimiter=", "
}


// { delimiter=""; printf "{" }
match($0, /^bm_([^[:blank:]]*)/, data) { field_str("program", data[1]) }
match($0, /([^[:blank:]]*[.]agda)/, data) { field_str("file", data[1]) }

# Sharing
/--sharing/ { field_lit("sharing", 1) }
/--no-sharing/ { field_lit("sharing", 0) }

# WHNF subst
/--whnfApplySubst/ { field_lit("whnf-apply-subst", 1) }
/--whnfEliminate/ { field_lit("whnf-eliminate", 1) }
/--disableSynEquality/ { field_lit("syn-equality", 0) }

/bm_tog/ && !/--whnfApplySubst/ { field_lit("whnf-apply-subst", 0) }
/bm_tog/ && !/--whnfEliminate/ { field_lit("whnf-eliminate", 0) }
/bm_tog/ && !/--disableSynEquality/ { field_lit("syn-equality", 1) }



match($0, /--termType[[:blank:]]*([A-Z]*)/, data) { field_str("term_repr", data[1]) }

# Times in ms
// { for(i=1;i<NF;i++) { 
        if (match($i, /([^[:blank:]]+):([^[:blank:]]*)ms/, data)) {  
            field_lit(data[1], gensub(/[,.]/, "", "g", data[2])) 
        } 
    }
}

match($0, /error:([^[:blank:]]+)/, data) { field_lit("error", data[1]) }
match($0, /feature:([^[:blank:]]+)/, data) { field_str("feature", data[1]) }
// { printf "}\n" }
