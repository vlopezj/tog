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
/--sharing/ { field_lit("sharing", 1) }
/--no-sharing/ { field_lit("sharing", 0) }
match($0, /--termType[[:blank:]]*([A-Z]*)/, data) { field_str("term_repr", data[1]) }
match($0, /time:([^[:blank:]]*)ms/, data) {  field_lit("time_ms", gensub(/[,.]/, "", "g", data[1])) }
match($0, /error:([^[:blank:]]*)/, data) { field_lit("error", data[1]) }
// { printf "}\n" }
