module.exports = function(grunt) {

  // Project configuration.
  grunt.initConfig({
    pkg: grunt.file.readJSON('package.json'),
    watch: {
      scripts: {
        files: ['0002-crypto-conditions/0002-crypto-conditions.md'],
        tasks: ['kramdown_rfc2629'],
        options: {
          spawn: false,
        },
      },
    },
    kramdown_rfc2629: {
      options: {
        outputs: ['text', 'html'],
        outputDir: '0002-crypto-conditions/output',
        removeXML: false
      },
      your_target: {
        src: ['0002-crypto-conditions/0002-crypto-conditions.md']
      },
    },
  });

  grunt.loadNpmTasks('grunt-contrib-watch');
  grunt.loadNpmTasks('grunt-kramdown-rfc2629');

};