.PRECIOUS: %.result.plain

%.result.plain:  %.test test-lib
	./$< | tee $@

%.result.json: %.result.plain features.gawk
	cat $< | gawk -f features.gawk > $@

fieldList: features.gawk features_fields.gawk
	cat $< | gawk -f features_fields.gawk > $@

%.result.csv: %.result.json fieldList
	cat $< | json2csv -l fieldList --ldjson -o $@ 
