import assert from 'node:assert/strict';
import {readFile, writeFile} from 'node:fs/promises';
import {existsSync, realpathSync} from 'node:fs';
import {createRequire} from 'node:module';
import {delimiter, join, resolve} from 'node:path';

const folder = resolve('goals/proof-recording-under-5x/comparison');
const rows = JSON.parse(await readFile(join(folder, 'full-cohort-ratios.json'), 'utf8'));
const spec = JSON.parse(await readFile(join(folder, 'recording-before-after.vl.json'), 'utf8'));
const cohort = JSON.parse(await readFile(join(folder, '../cohort.json'), 'utf8')).workloads;
const accepted = JSON.parse(await readFile(join(folder, '../final-acceptance.json'), 'utf8'));
assert.equal(rows.length, 508);
const cli = process.env.PATH.split(delimiter).map(path => join(path, 'vl2svg')).find(existsSync);
assert.ok(cli);
const toolkit = createRequire(realpathSync(cli));
const vega = await import(toolkit.resolve('vega'));
const {compile} = await import(toolkit.resolve('vega-lite'));
const warnings = [];
const logger = vega.logger(vega.Warn, undefined, (...args) => warnings.push(args));
spec.data = {values: rows};
const runtime = compile(spec, {logger}).spec;
const cdfData = runtime.data.find(data => data.transform?.some(transform => transform.as === 'cdf'));
assert.ok(cdfData);
const view = new vega.View(vega.parse(runtime), {renderer: 'none', logger});
try {
  await view.runAsync();
  assert.deepEqual(warnings, []);
  assert.deepEqual(view.scale('x').domain(), [1, 7.1]);
  assert.deepEqual(view.scale('y').domain(), [0, 1.03]);
  const transformed = view.data(cdfData.name);
  assert.equal(transformed.length, 508);
  const groups = [];
  for (const [metric, currentKey, paperKey] of [
    ['Runtime', 'wall_sec', 'paper_runtime_ratio'],
    ['Peak RSS', 'max_rss_bytes', 'paper_memory_ratio'],
  ]) {
    for (const version of ['Before · paper, Nov 4', 'After · optimized, Nov 8']) {
      const items = transformed.filter(row => row.metric === metric && row.version === version);
      assert.equal(items.length, 127);
      assert.deepEqual(new Set(items.map(row => row.workload_id)), new Set(cohort.map(row => row.logical_id)));
      items.sort((a, b) => a.rank - b.rank);
      for (const [index, row] of items.entries()) {
        const expected = version.startsWith('Before')
          ? cohort.find(item => item.logical_id === row.workload_id)[paperKey]
          : accepted.results.find(item => item.logical_id === row.workload_id).metrics[currentKey].ratio.point;
        assert.equal(row.ratio, expected);
        assert.equal(row.cohort_n, 127);
        assert.equal(row.rank, index + 1);
        assert.equal(row.cdf, (index + 1) / 127);
      }
      groups.push({metric, version, points: 127, maximum: items.at(-1).ratio});
    }
  }
  const endpoints = [];
  function visit(item) {
    if (item.mark?.marktype === 'symbol' && item.datum?.workload_id) endpoints.push(item);
    for (const child of item.items ?? []) visit(child);
  }
  visit(view.scenegraph().root);
  assert.equal(endpoints.length, 4);
  for (const item of endpoints) {
    assert.equal(item.datum.cdf, 1);
    assert.ok(item.bounds.x1 >= 0 && item.bounds.x2 <= item.mark.group.width);
    assert.ok(item.bounds.y1 >= 0 && item.bounds.y2 <= item.mark.group.height);
  }
  const summary = {
    passed: true,
    plotted_ratios: 508,
    groups,
    executed_x_domain: view.scale('x').domain(),
    executed_y_domain: view.scale('y').domain(),
    all_four_maximum_markers_in_bounds: true,
    warnings,
  };
  await writeFile(join(folder, 'plot-audit.json'), JSON.stringify(summary, null, 2) + '\n');
  console.log(JSON.stringify(summary, null, 2));
} finally {
  view.finalize();
}
