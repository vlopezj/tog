require(plyr)

d <- read.csv("all.20160216.result.csv")

v <- d[d$feature == "Total" & d$program == "tog" & d$error == 0 & d$time >= 100,]


baseline <- function (r) {
  r$syn.equality == 0 &
    r$whnf.apply.subst == 0 &
    r$whnf.eliminate == 0 &
    r$term_repr == "S"
}

f_time <- daply(v, .(file), function(r) {  r[baseline(r),]$time[1] })

v$time_norm <- (v$time / f_time[v$file])

v <- within(v, term_repr <- relevel(factor(term_repr), ref = "S"))

l <- lm(time_norm ~ syn.equality + whnf.apply.subst + whnf.eliminate + term_repr, v)

print(l)
print(anova(l))