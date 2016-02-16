.PRECIOUS: %.log
.PHONY: task-%

# Phony rules
task-%: %.test
	mkdir -p exp/$*/
	./$< | ./tasks.sh ./exp/$*/

%.log: %.task
	./bm.sh $< > $@

bm_tog_%.plain: bm_tog_%.log bm_tog_%.task
	./test-lib.sh pp_bm_tog < $< | ./test-lib.sh add_prefix $(word 2,$^) > $@

bm_agda_%.plain: bm_agda_%.log bm_agda_%.task
	./test-lib.sh pp_bm_agda < $< | ./test-lib.sh add_prefix $(word 2,$^) > $@

%.result.plain: exp/%/
	cat exp/$*/*.plain > $@

%.result.json: %.result.plain features.gawk
	cat $< | gawk -f features.gawk > $@

%.fieldList: %.result.json features_fields.gawk
	cat $< | gawk -f features_fields.gawk > $@

%.result.csv: %.result.json %.fieldList
	cat $< | json2csv -l $*.fieldList --ldjson -o $@ 
