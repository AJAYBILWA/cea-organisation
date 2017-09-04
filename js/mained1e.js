/** vim: et:ts=4:sw=4:sts=4
 * @license RequireJS 2.1.17 Copyright (c) 2010-2015, The Dojo Foundation All Rights Reserved.
 * Available via the MIT or new BSD license.
 * see: http://github.com/jrburke/requirejs for details
 */
//Not using strict: uneven strict support in browsers, #392, and causes
//problems with requirejs.exec()/transpiler plugins that may not be strict.
/*jslint regexp: true, nomen: true, sloppy: true */
/*global window, navigator, document, importScripts, setTimeout, opera */


var requirejs, require, define;
(function (global) {
    var req, s, head, baseElement, dataMain, src,
        interactiveScript, currentlyAddingScript, mainScript, subPath,
        version = '2.1.17',
        commentRegExp = /(\/\*([\s\S]*?)\*\/|([^:]|^)\/\/(.*)$)/mg,
        cjsRequireRegExp = /[^.]\s*require\s*\(\s*["']([^'"\s]+)["']\s*\)/g,
        jsSuffixRegExp = /\.js$/,
        currDirRegExp = /^\.\//,
        op = Object.prototype,
        ostring = op.toString,
        hasOwn = op.hasOwnProperty,
        ap = Array.prototype,
        apsp = ap.splice,
        isBrowser = !!(typeof window !== 'undefined' && typeof navigator !== 'undefined' && window.document),
        isWebWorker = !isBrowser && typeof importScripts !== 'undefined',
        //PS3 indicates loaded and complete, but need to wait for complete
        //specifically. Sequence is 'loading', 'loaded', execution,
        // then 'complete'. The UA check is unfortunate, but not sure how
        //to feature test w/o causing perf issues.
        readyRegExp = isBrowser && navigator.platform === 'PLAYSTATION 3' ?
                      /^complete$/ : /^(complete|loaded)$/,
        defContextName = '_',
        //Oh the tragedy, detecting opera. See the usage of isOpera for reason.
        isOpera = typeof opera !== 'undefined' && opera.toString() === '[object Opera]',
        contexts = {},
        cfg = {},
        globalDefQueue = [],
        useInteractive = false;

    function isFunction(it) {
        return ostring.call(it) === '[object Function]';
    }

    function isArray(it) {
        return ostring.call(it) === '[object Array]';
    }

    /**
     * Helper function for iterating over an array. If the func returns
     * a true value, it will break out of the loop.
     */
    function each(ary, func) {
        if (ary) {
            var i;
            for (i = 0; i < ary.length; i += 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    /**
     * Helper function for iterating over an array backwards. If the func
     * returns a true value, it will break out of the loop.
     */
    function eachReverse(ary, func) {
        if (ary) {
            var i;
            for (i = ary.length - 1; i > -1; i -= 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    function hasProp(obj, prop) {
        return hasOwn.call(obj, prop);
    }

    function getOwn(obj, prop) {
        return hasProp(obj, prop) && obj[prop];
    }

    /**
     * Cycles over properties in an object and calls a function for each
     * property value. If the function returns a truthy value, then the
     * iteration is stopped.
     */
    function eachProp(obj, func) {
        var prop;
        for (prop in obj) {
            if (hasProp(obj, prop)) {
                if (func(obj[prop], prop)) {
                    break;
                }
            }
        }
    }

    /**
     * Simple function to mix in properties from source into target,
     * but only if target does not already have a property of the same name.
     */
    function mixin(target, source, force, deepStringMixin) {
        if (source) {
            eachProp(source, function (value, prop) {
                if (force || !hasProp(target, prop)) {
                    if (deepStringMixin && typeof value === 'object' && value &&
                        !isArray(value) && !isFunction(value) &&
                        !(value instanceof RegExp)) {

                        if (!target[prop]) {
                            target[prop] = {};
                        }
                        mixin(target[prop], value, force, deepStringMixin);
                    } else {
                        target[prop] = value;
                    }
                }
            });
        }
        return target;
    }

    //Similar to Function.prototype.bind, but the 'this' object is specified
    //first, since it is easier to read/figure out what 'this' will be.
    function bind(obj, fn) {
        return function () {
            return fn.apply(obj, arguments);
        };
    }

    function scripts() {
        return document.getElementsByTagName('script');
    }

    function defaultOnError(err) {
        throw err;
    }

    //Allow getting a global that is expressed in
    //dot notation, like 'a.b.c'.
    function getGlobal(value) {
        if (!value) {
            return value;
        }
        var g = global;
        each(value.split('.'), function (part) {
            g = g[part];
        });
        return g;
    }

    /**
     * Constructs an error with a pointer to an URL with more information.
     * @param {String} id the error ID that maps to an ID on a web page.
     * @param {String} message human readable error.
     * @param {Error} [err] the original error, if there is one.
     *
     * @returns {Error}
     */
    function makeError(id, msg, err, requireModules) {
        var e = new Error(msg + '\nhttp://requirejs.org/docs/errors.html#' + id);
        e.requireType = id;
        e.requireModules = requireModules;
        if (err) {
            e.originalError = err;
        }
        return e;
    }

    if (typeof define !== 'undefined') {
        //If a define is already in play via another AMD loader,
        //do not overwrite.
        return;
    }

    if (typeof requirejs !== 'undefined') {
        if (isFunction(requirejs)) {
            //Do not overwrite an existing requirejs instance.
            return;
        }
        cfg = requirejs;
        requirejs = undefined;
    }

    //Allow for a require config object
    if (typeof require !== 'undefined' && !isFunction(require)) {
        //assume it is a config object.
        cfg = require;
        require = undefined;
    }

    function newContext(contextName) {
        var inCheckLoaded, Module, context, handlers,
            checkLoadedTimeoutId,
            config = {
                //Defaults. Do not set a default for map
                //config to speed up normalize(), which
                //will run faster if there is no default.
                waitSeconds: 7,
                baseUrl: './',
                paths: {},
                bundles: {},
                pkgs: {},
                shim: {},
                config: {}
            },
            registry = {},
            //registry of just enabled modules, to speed
            //cycle breaking code when lots of modules
            //are registered, but not activated.
            enabledRegistry = {},
            undefEvents = {},
            defQueue = [],
            defined = {},
            urlFetched = {},
            bundlesMap = {},
            requireCounter = 1,
            unnormalizedCounter = 1;

        /**
         * Trims the . and .. from an array of path segments.
         * It will keep a leading path segment if a .. will become
         * the first path segment, to help with module name lookups,
         * which act like paths, but can be remapped. But the end result,
         * all paths that use this function should look normalized.
         * NOTE: this method MODIFIES the input array.
         * @param {Array} ary the array of path segments.
         */
        function trimDots(ary) {
            var i, part;
            for (i = 0; i < ary.length; i++) {
                part = ary[i];
                if (part === '.') {
                    ary.splice(i, 1);
                    i -= 1;
                } else if (part === '..') {
                    // If at the start, or previous value is still ..,
                    // keep them so that when converted to a path it may
                    // still work when converted to a path, even though
                    // as an ID it is less than ideal. In larger point
                    // releases, may be better to just kick out an error.
                    if (i === 0 || (i === 1 && ary[2] === '..') || ary[i - 1] === '..') {
                        continue;
                    } else if (i > 0) {
                        ary.splice(i - 1, 2);
                        i -= 2;
                    }
                }
            }
        }

        /**
         * Given a relative module name, like ./something, normalize it to
         * a real name that can be mapped to a path.
         * @param {String} name the relative name
         * @param {String} baseName a real name that the name arg is relative
         * to.
         * @param {Boolean} applyMap apply the map config to the value. Should
         * only be done if this normalization is for a dependency ID.
         * @returns {String} normalized name
         */
        function normalize(name, baseName, applyMap) {
            var pkgMain, mapValue, nameParts, i, j, nameSegment, lastIndex,
                foundMap, foundI, foundStarMap, starI, normalizedBaseParts,
                baseParts = (baseName && baseName.split('/')),
                map = config.map,
                starMap = map && map['*'];

            //Adjust any relative paths.
            if (name) {
                name = name.split('/');
                lastIndex = name.length - 1;

                // If wanting node ID compatibility, strip .js from end
                // of IDs. Have to do this here, and not in nameToUrl
                // because node allows either .js or non .js to map
                // to same file.
                if (config.nodeIdCompat && jsSuffixRegExp.test(name[lastIndex])) {
                    name[lastIndex] = name[lastIndex].replace(jsSuffixRegExp, '');
                }

                // Starts with a '.' so need the baseName
                if (name[0].charAt(0) === '.' && baseParts) {
                    //Convert baseName to array, and lop off the last part,
                    //so that . matches that 'directory' and not name of the baseName's
                    //module. For instance, baseName of 'one/two/three', maps to
                    //'one/two/three.js', but we want the directory, 'one/two' for
                    //this normalization.
                    normalizedBaseParts = baseParts.slice(0, baseParts.length - 1);
                    name = normalizedBaseParts.concat(name);
                }

                trimDots(name);
                name = name.join('/');
            }

            //Apply map config if available.
            if (applyMap && map && (baseParts || starMap)) {
                nameParts = name.split('/');

                outerLoop: for (i = nameParts.length; i > 0; i -= 1) {
                    nameSegment = nameParts.slice(0, i).join('/');

                    if (baseParts) {
                        //Find the longest baseName segment match in the config.
                        //So, do joins on the biggest to smallest lengths of baseParts.
                        for (j = baseParts.length; j > 0; j -= 1) {
                            mapValue = getOwn(map, baseParts.slice(0, j).join('/'));

                            //baseName segment has config, find if it has one for
                            //this name.
                            if (mapValue) {
                                mapValue = getOwn(mapValue, nameSegment);
                                if (mapValue) {
                                    //Match, update name to the new value.
                                    foundMap = mapValue;
                                    foundI = i;
                                    break outerLoop;
                                }
                            }
                        }
                    }

                    //Check for a star map match, but just hold on to it,
                    //if there is a shorter segment match later in a matching
                    //config, then favor over this star map.
                    if (!foundStarMap && starMap && getOwn(starMap, nameSegment)) {
                        foundStarMap = getOwn(starMap, nameSegment);
                        starI = i;
                    }
                }

                if (!foundMap && foundStarMap) {
                    foundMap = foundStarMap;
                    foundI = starI;
                }

                if (foundMap) {
                    nameParts.splice(0, foundI, foundMap);
                    name = nameParts.join('/');
                }
            }

            // If the name points to a package's name, use
            // the package main instead.
            pkgMain = getOwn(config.pkgs, name);

            return pkgMain ? pkgMain : name;
        }

        function removeScript(name) {
            if (isBrowser) {
                each(scripts(), function (scriptNode) {
                    if (scriptNode.getAttribute('data-requiremodule') === name &&
                            scriptNode.getAttribute('data-requirecontext') === context.contextName) {
                        scriptNode.parentNode.removeChild(scriptNode);
                        return true;
                    }
                });
            }
        }

        function hasPathFallback(id) {
            var pathConfig = getOwn(config.paths, id);
            if (pathConfig && isArray(pathConfig) && pathConfig.length > 1) {
                //Pop off the first array value, since it failed, and
                //retry
                pathConfig.shift();
                context.require.undef(id);

                //Custom require that does not do map translation, since
                //ID is "absolute", already mapped/resolved.
                context.makeRequire(null, {
                    skipMap: true
                })([id]);

                return true;
            }
        }

        //Turns a plugin!resource to [plugin, resource]
        //with the plugin being undefined if the name
        //did not have a plugin prefix.
        function splitPrefix(name) {
            var prefix,
                index = name ? name.indexOf('!') : -1;
            if (index > -1) {
                prefix = name.substring(0, index);
                name = name.substring(index + 1, name.length);
            }
            return [prefix, name];
        }

        /**
         * Creates a module mapping that includes plugin prefix, module
         * name, and path. If parentModuleMap is provided it will
         * also normalize the name via require.normalize()
         *
         * @param {String} name the module name
         * @param {String} [parentModuleMap] parent module map
         * for the module name, used to resolve relative names.
         * @param {Boolean} isNormalized: is the ID already normalized.
         * This is true if this call is done for a define() module ID.
         * @param {Boolean} applyMap: apply the map config to the ID.
         * Should only be true if this map is for a dependency.
         *
         * @returns {Object}
         */
        function makeModuleMap(name, parentModuleMap, isNormalized, applyMap) {
            var url, pluginModule, suffix, nameParts,
                prefix = null,
                parentName = parentModuleMap ? parentModuleMap.name : null,
                originalName = name,
                isDefine = true,
                normalizedName = '';

            //If no name, then it means it is a require call, generate an
            //internal name.
            if (!name) {
                isDefine = false;
                name = '_@r' + (requireCounter += 1);
            }

            nameParts = splitPrefix(name);
            prefix = nameParts[0];
            name = nameParts[1];

            if (prefix) {
                prefix = normalize(prefix, parentName, applyMap);
                pluginModule = getOwn(defined, prefix);
            }

            //Account for relative paths if there is a base name.
            if (name) {
                if (prefix) {
                    if (pluginModule && pluginModule.normalize) {
                        //Plugin is loaded, use its normalize method.
                        normalizedName = pluginModule.normalize(name, function (name) {
                            return normalize(name, parentName, applyMap);
                        });
                    } else {
                        // If nested plugin references, then do not try to
                        // normalize, as it will not normalize correctly. This
                        // places a restriction on resourceIds, and the longer
                        // term solution is not to normalize until plugins are
                        // loaded and all normalizations to allow for async
                        // loading of a loader plugin. But for now, fixes the
                        // common uses. Details in #1131
                        normalizedName = name.indexOf('!') === -1 ?
                                         normalize(name, parentName, applyMap) :
                                         name;
                    }
                } else {
                    //A regular module.
                    normalizedName = normalize(name, parentName, applyMap);

                    //Normalized name may be a plugin ID due to map config
                    //application in normalize. The map config values must
                    //already be normalized, so do not need to redo that part.
                    nameParts = splitPrefix(normalizedName);
                    prefix = nameParts[0];
                    normalizedName = nameParts[1];
                    isNormalized = true;

                    url = context.nameToUrl(normalizedName);
                }
            }

            //If the id is a plugin id that cannot be determined if it needs
            //normalization, stamp it with a unique ID so two matching relative
            //ids that may conflict can be separate.
            suffix = prefix && !pluginModule && !isNormalized ?
                     '_unnormalized' + (unnormalizedCounter += 1) :
                     '';

            return {
                prefix: prefix,
                name: normalizedName,
                parentMap: parentModuleMap,
                unnormalized: !!suffix,
                url: url,
                originalName: originalName,
                isDefine: isDefine,
                id: (prefix ?
                        prefix + '!' + normalizedName :
                        normalizedName) + suffix
            };
        }

        function getModule(depMap) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (!mod) {
                mod = registry[id] = new context.Module(depMap);
            }

            return mod;
        }

        function on(depMap, name, fn) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (hasProp(defined, id) &&
                    (!mod || mod.defineEmitComplete)) {
                if (name === 'defined') {
                    fn(defined[id]);
                }
            } else {
                mod = getModule(depMap);
                if (mod.error && name === 'error') {
                    fn(mod.error);
                } else {
                    mod.on(name, fn);
                }
            }
        }

        function onError(err, errback) {
            var ids = err.requireModules,
                notified = false;

            if (errback) {
                errback(err);
            } else {
                each(ids, function (id) {
                    var mod = getOwn(registry, id);
                    if (mod) {
                        //Set error on module, so it skips timeout checks.
                        mod.error = err;
                        if (mod.events.error) {
                            notified = true;
                            mod.emit('error', err);
                        }
                    }
                });

                if (!notified) {
                    req.onError(err);
                }
            }
        }

        /**
         * Internal method to transfer globalQueue items to this context's
         * defQueue.
         */
        function takeGlobalQueue() {
            //Push all the globalDefQueue items into the context's defQueue
            if (globalDefQueue.length) {
                //Array splice in the values since the context code has a
                //local var ref to defQueue, so cannot just reassign the one
                //on context.
                apsp.apply(defQueue,
                           [defQueue.length, 0].concat(globalDefQueue));
                globalDefQueue = [];
            }
        }

        handlers = {
            'require': function (mod) {
                if (mod.require) {
                    return mod.require;
                } else {
                    return (mod.require = context.makeRequire(mod.map));
                }
            },
            'exports': function (mod) {
                mod.usingExports = true;
                if (mod.map.isDefine) {
                    if (mod.exports) {
                        return (defined[mod.map.id] = mod.exports);
                    } else {
                        return (mod.exports = defined[mod.map.id] = {});
                    }
                }
            },
            'module': function (mod) {
                if (mod.module) {
                    return mod.module;
                } else {
                    return (mod.module = {
                        id: mod.map.id,
                        uri: mod.map.url,
                        config: function () {
                            return  getOwn(config.config, mod.map.id) || {};
                        },
                        exports: mod.exports || (mod.exports = {})
                    });
                }
            }
        };

        function cleanRegistry(id) {
            //Clean up machinery used for waiting modules.
            delete registry[id];
            delete enabledRegistry[id];
        }

        function breakCycle(mod, traced, processed) {
            var id = mod.map.id;

            if (mod.error) {
                mod.emit('error', mod.error);
            } else {
                traced[id] = true;
                each(mod.depMaps, function (depMap, i) {
                    var depId = depMap.id,
                        dep = getOwn(registry, depId);

                    //Only force things that have not completed
                    //being defined, so still in the registry,
                    //and only if it has not been matched up
                    //in the module already.
                    if (dep && !mod.depMatched[i] && !processed[depId]) {
                        if (getOwn(traced, depId)) {
                            mod.defineDep(i, defined[depId]);
                            mod.check(); //pass false?
                        } else {
                            breakCycle(dep, traced, processed);
                        }
                    }
                });
                processed[id] = true;
            }
        }

        function checkLoaded() {
            var err, usingPathFallback,
                waitInterval = config.waitSeconds * 1000,
                //It is possible to disable the wait interval by using waitSeconds of 0.
                expired = waitInterval && (context.startTime + waitInterval) < new Date().getTime(),
                noLoads = [],
                reqCalls = [],
                stillLoading = false,
                needCycleCheck = true;

            //Do not bother if this call was a result of a cycle break.
            if (inCheckLoaded) {
                return;
            }

            inCheckLoaded = true;

            //Figure out the state of all the modules.
            eachProp(enabledRegistry, function (mod) {
                var map = mod.map,
                    modId = map.id;

                //Skip things that are not enabled or in error state.
                if (!mod.enabled) {
                    return;
                }

                if (!map.isDefine) {
                    reqCalls.push(mod);
                }

                if (!mod.error) {
                    //If the module should be executed, and it has not
                    //been inited and time is up, remember it.
                    if (!mod.inited && expired) {
                        if (hasPathFallback(modId)) {
                            usingPathFallback = true;
                            stillLoading = true;
                        } else {
                            noLoads.push(modId);
                            removeScript(modId);
                        }
                    } else if (!mod.inited && mod.fetched && map.isDefine) {
                        stillLoading = true;
                        if (!map.prefix) {
                            //No reason to keep looking for unfinished
                            //loading. If the only stillLoading is a
                            //plugin resource though, keep going,
                            //because it may be that a plugin resource
                            //is waiting on a non-plugin cycle.
                            return (needCycleCheck = false);
                        }
                    }
                }
            });

            if (expired && noLoads.length) {
                //If wait time expired, throw error of unloaded modules.
                err = makeError('timeout', 'Load timeout for modules: ' + noLoads, null, noLoads);
                err.contextName = context.contextName;
                return onError(err);
            }

            //Not expired, check for a cycle.
            if (needCycleCheck) {
                each(reqCalls, function (mod) {
                    breakCycle(mod, {}, {});
                });
            }

            //If still waiting on loads, and the waiting load is something
            //other than a plugin resource, or there are still outstanding
            //scripts, then just try back later.
            if ((!expired || usingPathFallback) && stillLoading) {
                //Something is still waiting to load. Wait for it, but only
                //if a timeout is not already in effect.
                if ((isBrowser || isWebWorker) && !checkLoadedTimeoutId) {
                    checkLoadedTimeoutId = setTimeout(function () {
                        checkLoadedTimeoutId = 0;
                        checkLoaded();
                    }, 50);
                }
            }

            inCheckLoaded = false;
        }

        Module = function (map) {
            this.events = getOwn(undefEvents, map.id) || {};
            this.map = map;
            this.shim = getOwn(config.shim, map.id);
            this.depExports = [];
            this.depMaps = [];
            this.depMatched = [];
            this.pluginMaps = {};
            this.depCount = 0;

            /* this.exports this.factory
               this.depMaps = [],
               this.enabled, this.fetched
            */
        };

        Module.prototype = {
            init: function (depMaps, factory, errback, options) {
                options = options || {};

                //Do not do more inits if already done. Can happen if there
                //are multiple define calls for the same module. That is not
                //a normal, common case, but it is also not unexpected.
                if (this.inited) {
                    return;
                }

                this.factory = factory;

                if (errback) {
                    //Register for errors on this module.
                    this.on('error', errback);
                } else if (this.events.error) {
                    //If no errback already, but there are error listeners
                    //on this module, set up an errback to pass to the deps.
                    errback = bind(this, function (err) {
                        this.emit('error', err);
                    });
                }

                //Do a copy of the dependency array, so that
                //source inputs are not modified. For example
                //"shim" deps are passed in here directly, and
                //doing a direct modification of the depMaps array
                //would affect that config.
                this.depMaps = depMaps && depMaps.slice(0);

                this.errback = errback;

                //Indicate this module has be initialized
                this.inited = true;

                this.ignore = options.ignore;

                //Could have option to init this module in enabled mode,
                //or could have been previously marked as enabled. However,
                //the dependencies are not known until init is called. So
                //if enabled previously, now trigger dependencies as enabled.
                if (options.enabled || this.enabled) {
                    //Enable this module and dependencies.
                    //Will call this.check()
                    this.enable();
                } else {
                    this.check();
                }
            },

            defineDep: function (i, depExports) {
                //Because of cycles, defined callback for a given
                //export can be called more than once.
                if (!this.depMatched[i]) {
                    this.depMatched[i] = true;
                    this.depCount -= 1;
                    this.depExports[i] = depExports;
                }
            },

            fetch: function () {
                if (this.fetched) {
                    return;
                }
                this.fetched = true;

                context.startTime = (new Date()).getTime();

                var map = this.map;

                //If the manager is for a plugin managed resource,
                //ask the plugin to load it now.
                if (this.shim) {
                    context.makeRequire(this.map, {
                        enableBuildCallback: true
                    })(this.shim.deps || [], bind(this, function () {
                        return map.prefix ? this.callPlugin() : this.load();
                    }));
                } else {
                    //Regular dependency.
                    return map.prefix ? this.callPlugin() : this.load();
                }
            },

            load: function () {
                var url = this.map.url;

                //Regular dependency.
                if (!urlFetched[url]) {
                    urlFetched[url] = true;
                    context.load(this.map.id, url);
                }
            },

            /**
             * Checks if the module is ready to define itself, and if so,
             * define it.
             */
            check: function () {
                if (!this.enabled || this.enabling) {
                    return;
                }

                var err, cjsModule,
                    id = this.map.id,
                    depExports = this.depExports,
                    exports = this.exports,
                    factory = this.factory;

                if (!this.inited) {
                    this.fetch();
                } else if (this.error) {
                    this.emit('error', this.error);
                } else if (!this.defining) {
                    //The factory could trigger another require call
                    //that would result in checking this module to
                    //define itself again. If already in the process
                    //of doing that, skip this work.
                    this.defining = true;

                    if (this.depCount < 1 && !this.defined) {
                        if (isFunction(factory)) {
                            //If there is an error listener, favor passing
                            //to that instead of throwing an error. However,
                            //only do it for define()'d  modules. require
                            //errbacks should not be called for failures in
                            //their callbacks (#699). However if a global
                            //onError is set, use that.
                            if ((this.events.error && this.map.isDefine) ||
                                req.onError !== defaultOnError) {
                                try {
                                    exports = context.execCb(id, factory, depExports, exports);
                                } catch (e) {
                                    err = e;
                                }
                            } else {
                                exports = context.execCb(id, factory, depExports, exports);
                            }

                            // Favor return value over exports. If node/cjs in play,
                            // then will not have a return value anyway. Favor
                            // module.exports assignment over exports object.
                            if (this.map.isDefine && exports === undefined) {
                                cjsModule = this.module;
                                if (cjsModule) {
                                    exports = cjsModule.exports;
                                } else if (this.usingExports) {
                                    //exports already set the defined value.
                                    exports = this.exports;
                                }
                            }

                            if (err) {
                                err.requireMap = this.map;
                                err.requireModules = this.map.isDefine ? [this.map.id] : null;
                                err.requireType = this.map.isDefine ? 'define' : 'require';
                                return onError((this.error = err));
                            }

                        } else {
                            //Just a literal value
                            exports = factory;
                        }

                        this.exports = exports;

                        if (this.map.isDefine && !this.ignore) {
                            defined[id] = exports;

                            if (req.onResourceLoad) {
                                req.onResourceLoad(context, this.map, this.depMaps);
                            }
                        }

                        //Clean up
                        cleanRegistry(id);

                        this.defined = true;
                    }

                    //Finished the define stage. Allow calling check again
                    //to allow define notifications below in the case of a
                    //cycle.
                    this.defining = false;

                    if (this.defined && !this.defineEmitted) {
                        this.defineEmitted = true;
                        this.emit('defined', this.exports);
                        this.defineEmitComplete = true;
                    }

                }
            },

            callPlugin: function () {
                var map = this.map,
                    id = map.id,
                    //Map already normalized the prefix.
                    pluginMap = makeModuleMap(map.prefix);

                //Mark this as a dependency for this plugin, so it
                //can be traced for cycles.
                this.depMaps.push(pluginMap);

                on(pluginMap, 'defined', bind(this, function (plugin) {
                    var load, normalizedMap, normalizedMod,
                        bundleId = getOwn(bundlesMap, this.map.id),
                        name = this.map.name,
                        parentName = this.map.parentMap ? this.map.parentMap.name : null,
                        localRequire = context.makeRequire(map.parentMap, {
                            enableBuildCallback: true
                        });

                    //If current map is not normalized, wait for that
                    //normalized name to load instead of continuing.
                    if (this.map.unnormalized) {
                        //Normalize the ID if the plugin allows it.
                        if (plugin.normalize) {
                            name = plugin.normalize(name, function (name) {
                                return normalize(name, parentName, true);
                            }) || '';
                        }

                        //prefix and name should already be normalized, no need
                        //for applying map config again either.
                        normalizedMap = makeModuleMap(map.prefix + '!' + name,
                                                      this.map.parentMap);
                        on(normalizedMap,
                            'defined', bind(this, function (value) {
                                this.init([], function () { return value; }, null, {
                                    enabled: true,
                                    ignore: true
                                });
                            }));

                        normalizedMod = getOwn(registry, normalizedMap.id);
                        if (normalizedMod) {
                            //Mark this as a dependency for this plugin, so it
                            //can be traced for cycles.
                            this.depMaps.push(normalizedMap);

                            if (this.events.error) {
                                normalizedMod.on('error', bind(this, function (err) {
                                    this.emit('error', err);
                                }));
                            }
                            normalizedMod.enable();
                        }

                        return;
                    }

                    //If a paths config, then just load that file instead to
                    //resolve the plugin, as it is built into that paths layer.
                    if (bundleId) {
                        this.map.url = context.nameToUrl(bundleId);
                        this.load();
                        return;
                    }

                    load = bind(this, function (value) {
                        this.init([], function () { return value; }, null, {
                            enabled: true
                        });
                    });

                    load.error = bind(this, function (err) {
                        this.inited = true;
                        this.error = err;
                        err.requireModules = [id];

                        //Remove temp unnormalized modules for this module,
                        //since they will never be resolved otherwise now.
                        eachProp(registry, function (mod) {
                            if (mod.map.id.indexOf(id + '_unnormalized') === 0) {
                                cleanRegistry(mod.map.id);
                            }
                        });

                        onError(err);
                    });

                    //Allow plugins to load other code without having to know the
                    //context or how to 'complete' the load.
                    load.fromText = bind(this, function (text, textAlt) {
                        /*jslint evil: true */
                        var moduleName = map.name,
                            moduleMap = makeModuleMap(moduleName),
                            hasInteractive = useInteractive;

                        //As of 2.1.0, support just passing the text, to reinforce
                        //fromText only being called once per resource. Still
                        //support old style of passing moduleName but discard
                        //that moduleName in favor of the internal ref.
                        if (textAlt) {
                            text = textAlt;
                        }

                        //Turn off interactive script matching for IE for any define
                        //calls in the text, then turn it back on at the end.
                        if (hasInteractive) {
                            useInteractive = false;
                        }

                        //Prime the system by creating a module instance for
                        //it.
                        getModule(moduleMap);

                        //Transfer any config to this other module.
                        if (hasProp(config.config, id)) {
                            config.config[moduleName] = config.config[id];
                        }

                        try {
                            req.exec(text);
                        } catch (e) {
                            return onError(makeError('fromtexteval',
                                             'fromText eval for ' + id +
                                            ' failed: ' + e,
                                             e,
                                             [id]));
                        }

                        if (hasInteractive) {
                            useInteractive = true;
                        }

                        //Mark this as a dependency for the plugin
                        //resource
                        this.depMaps.push(moduleMap);

                        //Support anonymous modules.
                        context.completeLoad(moduleName);

                        //Bind the value of that module to the value for this
                        //resource ID.
                        localRequire([moduleName], load);
                    });

                    //Use parentName here since the plugin's name is not reliable,
                    //could be some weird string with no path that actually wants to
                    //reference the parentName's path.
                    plugin.load(map.name, localRequire, load, config);
                }));

                context.enable(pluginMap, this);
                this.pluginMaps[pluginMap.id] = pluginMap;
            },

            enable: function () {
                enabledRegistry[this.map.id] = this;
                this.enabled = true;

                //Set flag mentioning that the module is enabling,
                //so that immediate calls to the defined callbacks
                //for dependencies do not trigger inadvertent load
                //with the depCount still being zero.
                this.enabling = true;

                //Enable each dependency
                each(this.depMaps, bind(this, function (depMap, i) {
                    var id, mod, handler;

                    if (typeof depMap === 'string') {
                        //Dependency needs to be converted to a depMap
                        //and wired up to this module.
                        depMap = makeModuleMap(depMap,
                                               (this.map.isDefine ? this.map : this.map.parentMap),
                                               false,
                                               !this.skipMap);
                        this.depMaps[i] = depMap;

                        handler = getOwn(handlers, depMap.id);

                        if (handler) {
                            this.depExports[i] = handler(this);
                            return;
                        }

                        this.depCount += 1;

                        on(depMap, 'defined', bind(this, function (depExports) {
                            this.defineDep(i, depExports);
                            this.check();
                        }));

                        if (this.errback) {
                            on(depMap, 'error', bind(this, this.errback));
                        } else if (this.events.error) {
                            // No direct errback on this module, but something
                            // else is listening for errors, so be sure to
                            // propagate the error correctly.
                            on(depMap, 'error', bind(this, function(err) {
                                this.emit('error', err);
                            }));
                        }
                    }

                    id = depMap.id;
                    mod = registry[id];

                    //Skip special modules like 'require', 'exports', 'module'
                    //Also, don't call enable if it is already enabled,
                    //important in circular dependency cases.
                    if (!hasProp(handlers, id) && mod && !mod.enabled) {
                        context.enable(depMap, this);
                    }
                }));

                //Enable each plugin that is used in
                //a dependency
                eachProp(this.pluginMaps, bind(this, function (pluginMap) {
                    var mod = getOwn(registry, pluginMap.id);
                    if (mod && !mod.enabled) {
                        context.enable(pluginMap, this);
                    }
                }));

                this.enabling = false;

                this.check();
            },

            on: function (name, cb) {
                var cbs = this.events[name];
                if (!cbs) {
                    cbs = this.events[name] = [];
                }
                cbs.push(cb);
            },

            emit: function (name, evt) {
                each(this.events[name], function (cb) {
                    cb(evt);
                });
                if (name === 'error') {
                    //Now that the error handler was triggered, remove
                    //the listeners, since this broken Module instance
                    //can stay around for a while in the registry.
                    delete this.events[name];
                }
            }
        };

        function callGetModule(args) {
            //Skip modules already defined.
            if (!hasProp(defined, args[0])) {
                getModule(makeModuleMap(args[0], null, true)).init(args[1], args[2]);
            }
        }

        function removeListener(node, func, name, ieName) {
            //Favor detachEvent because of IE9
            //issue, see attachEvent/addEventListener comment elsewhere
            //in this file.
            if (node.detachEvent && !isOpera) {
                //Probably IE. If not it will throw an error, which will be
                //useful to know.
                if (ieName) {
                    node.detachEvent(ieName, func);
                }
            } else {
                node.removeEventListener(name, func, false);
            }
        }

        /**
         * Given an event from a script node, get the requirejs info from it,
         * and then removes the event listeners on the node.
         * @param {Event} evt
         * @returns {Object}
         */
        function getScriptData(evt) {
            //Using currentTarget instead of target for Firefox 2.0's sake. Not
            //all old browsers will be supported, but this one was easy enough
            //to support and still makes sense.
            var node = evt.currentTarget || evt.srcElement;

            //Remove the listeners once here.
            removeListener(node, context.onScriptLoad, 'load', 'onreadystatechange');
            removeListener(node, context.onScriptError, 'error');

            return {
                node: node,
                id: node && node.getAttribute('data-requiremodule')
            };
        }

        function intakeDefines() {
            var args;

            //Any defined modules in the global queue, intake them now.
            takeGlobalQueue();

            //Make sure any remaining defQueue items get properly processed.
            while (defQueue.length) {
                args = defQueue.shift();
                if (args[0] === null) {
                    return onError(makeError('mismatch', 'Mismatched anonymous define() module: ' + args[args.length - 1]));
                } else {
                    //args are id, deps, factory. Should be normalized by the
                    //define() function.
                    callGetModule(args);
                }
            }
        }

        context = {
            config: config,
            contextName: contextName,
            registry: registry,
            defined: defined,
            urlFetched: urlFetched,
            defQueue: defQueue,
            Module: Module,
            makeModuleMap: makeModuleMap,
            nextTick: req.nextTick,
            onError: onError,

            /**
             * Set a configuration for the context.
             * @param {Object} cfg config object to integrate.
             */
            configure: function (cfg) {
                //Make sure the baseUrl ends in a slash.
                if (cfg.baseUrl) {
                    if (cfg.baseUrl.charAt(cfg.baseUrl.length - 1) !== '/') {
                        cfg.baseUrl += '/';
                    }
                }

                //Save off the paths since they require special processing,
                //they are additive.
                var shim = config.shim,
                    objs = {
                        paths: true,
                        bundles: true,
                        config: true,
                        map: true
                    };

                eachProp(cfg, function (value, prop) {
                    if (objs[prop]) {
                        if (!config[prop]) {
                            config[prop] = {};
                        }
                        mixin(config[prop], value, true, true);
                    } else {
                        config[prop] = value;
                    }
                });

                //Reverse map the bundles
                if (cfg.bundles) {
                    eachProp(cfg.bundles, function (value, prop) {
                        each(value, function (v) {
                            if (v !== prop) {
                                bundlesMap[v] = prop;
                            }
                        });
                    });
                }

                //Merge shim
                if (cfg.shim) {
                    eachProp(cfg.shim, function (value, id) {
                        //Normalize the structure
                        if (isArray(value)) {
                            value = {
                                deps: value
                            };
                        }
                        if ((value.exports || value.init) && !value.exportsFn) {
                            value.exportsFn = context.makeShimExports(value);
                        }
                        shim[id] = value;
                    });
                    config.shim = shim;
                }

                //Adjust packages if necessary.
                if (cfg.packages) {
                    each(cfg.packages, function (pkgObj) {
                        var location, name;

                        pkgObj = typeof pkgObj === 'string' ? { name: pkgObj } : pkgObj;

                        name = pkgObj.name;
                        location = pkgObj.location;
                        if (location) {
                            config.paths[name] = pkgObj.location;
                        }

                        //Save pointer to main module ID for pkg name.
                        //Remove leading dot in main, so main paths are normalized,
                        //and remove any trailing .js, since different package
                        //envs have different conventions: some use a module name,
                        //some use a file name.
                        config.pkgs[name] = pkgObj.name + '/' + (pkgObj.main || 'main')
                                     .replace(currDirRegExp, '')
                                     .replace(jsSuffixRegExp, '');
                    });
                }

                //If there are any "waiting to execute" modules in the registry,
                //update the maps for them, since their info, like URLs to load,
                //may have changed.
                eachProp(registry, function (mod, id) {
                    //If module already has init called, since it is too
                    //late to modify them, and ignore unnormalized ones
                    //since they are transient.
                    if (!mod.inited && !mod.map.unnormalized) {
                        mod.map = makeModuleMap(id);
                    }
                });

                //If a deps array or a config callback is specified, then call
                //require with those args. This is useful when require is defined as a
                //config object before require.js is loaded.
                if (cfg.deps || cfg.callback) {
                    context.require(cfg.deps || [], cfg.callback);
                }
            },

            makeShimExports: function (value) {
                function fn() {
                    var ret;
                    if (value.init) {
                        ret = value.init.apply(global, arguments);
                    }
                    return ret || (value.exports && getGlobal(value.exports));
                }
                return fn;
            },

            makeRequire: function (relMap, options) {
                options = options || {};

                function localRequire(deps, callback, errback) {
                    var id, map, requireMod;

                    if (options.enableBuildCallback && callback && isFunction(callback)) {
                        callback.__requireJsBuild = true;
                    }

                    if (typeof deps === 'string') {
                        if (isFunction(callback)) {
                            //Invalid call
                            return onError(makeError('requireargs', 'Invalid require call'), errback);
                        }

                        //If require|exports|module are requested, get the
                        //value for them from the special handlers. Caveat:
                        //this only works while module is being defined.
                        if (relMap && hasProp(handlers, deps)) {
                            return handlers[deps](registry[relMap.id]);
                        }

                        //Synchronous access to one module. If require.get is
                        //available (as in the Node adapter), prefer that.
                        if (req.get) {
                            return req.get(context, deps, relMap, localRequire);
                        }

                        //Normalize module name, if it contains . or ..
                        map = makeModuleMap(deps, relMap, false, true);
                        id = map.id;

                        if (!hasProp(defined, id)) {
                            return onError(makeError('notloaded', 'Module name "' +
                                        id +
                                        '" has not been loaded yet for context: ' +
                                        contextName +
                                        (relMap ? '' : '. Use require([])')));
                        }
                        return defined[id];
                    }

                    //Grab defines waiting in the global queue.
                    intakeDefines();

                    //Mark all the dependencies as needing to be loaded.
                    context.nextTick(function () {
                        //Some defines could have been added since the
                        //require call, collect them.
                        intakeDefines();

                        requireMod = getModule(makeModuleMap(null, relMap));

                        //Store if map config should be applied to this require
                        //call for dependencies.
                        requireMod.skipMap = options.skipMap;

                        requireMod.init(deps, callback, errback, {
                            enabled: true
                        });

                        checkLoaded();
                    });

                    return localRequire;
                }

                mixin(localRequire, {
                    isBrowser: isBrowser,

                    /**
                     * Converts a module name + .extension into an URL path.
                     * *Requires* the use of a module name. It does not support using
                     * plain URLs like nameToUrl.
                     */
                    toUrl: function (moduleNamePlusExt) {
                        var ext,
                            index = moduleNamePlusExt.lastIndexOf('.'),
                            segment = moduleNamePlusExt.split('/')[0],
                            isRelative = segment === '.' || segment === '..';

                        //Have a file extension alias, and it is not the
                        //dots from a relative path.
                        if (index !== -1 && (!isRelative || index > 1)) {
                            ext = moduleNamePlusExt.substring(index, moduleNamePlusExt.length);
                            moduleNamePlusExt = moduleNamePlusExt.substring(0, index);
                        }

                        return context.nameToUrl(normalize(moduleNamePlusExt,
                                                relMap && relMap.id, true), ext,  true);
                    },

                    defined: function (id) {
                        return hasProp(defined, makeModuleMap(id, relMap, false, true).id);
                    },

                    specified: function (id) {
                        id = makeModuleMap(id, relMap, false, true).id;
                        return hasProp(defined, id) || hasProp(registry, id);
                    }
                });

                //Only allow undef on top level require calls
                if (!relMap) {
                    localRequire.undef = function (id) {
                        //Bind any waiting define() calls to this context,
                        //fix for #408
                        takeGlobalQueue();

                        var map = makeModuleMap(id, relMap, true),
                            mod = getOwn(registry, id);

                        removeScript(id);

                        delete defined[id];
                        delete urlFetched[map.url];
                        delete undefEvents[id];

                        //Clean queued defines too. Go backwards
                        //in array so that the splices do not
                        //mess up the iteration.
                        eachReverse(defQueue, function(args, i) {
                            if(args[0] === id) {
                                defQueue.splice(i, 1);
                            }
                        });

                        if (mod) {
                            //Hold on to listeners in case the
                            //module will be attempted to be reloaded
                            //using a different config.
                            if (mod.events.defined) {
                                undefEvents[id] = mod.events;
                            }

                            cleanRegistry(id);
                        }
                    };
                }

                return localRequire;
            },

            /**
             * Called to enable a module if it is still in the registry
             * awaiting enablement. A second arg, parent, the parent module,
             * is passed in for context, when this method is overridden by
             * the optimizer. Not shown here to keep code compact.
             */
            enable: function (depMap) {
                var mod = getOwn(registry, depMap.id);
                if (mod) {
                    getModule(depMap).enable();
                }
            },

            /**
             * Internal method used by environment adapters to complete a load event.
             * A load event could be a script load or just a load pass from a synchronous
             * load call.
             * @param {String} moduleName the name of the module to potentially complete.
             */
            completeLoad: function (moduleName) {
                var found, args, mod,
                    shim = getOwn(config.shim, moduleName) || {},
                    shExports = shim.exports;

                takeGlobalQueue();

                while (defQueue.length) {
                    args = defQueue.shift();
                    if (args[0] === null) {
                        args[0] = moduleName;
                        //If already found an anonymous module and bound it
                        //to this name, then this is some other anon module
                        //waiting for its completeLoad to fire.
                        if (found) {
                            break;
                        }
                        found = true;
                    } else if (args[0] === moduleName) {
                        //Found matching define call for this script!
                        found = true;
                    }

                    callGetModule(args);
                }

                //Do this after the cycle of callGetModule in case the result
                //of those calls/init calls changes the registry.
                mod = getOwn(registry, moduleName);

                if (!found && !hasProp(defined, moduleName) && mod && !mod.inited) {
                    if (config.enforceDefine && (!shExports || !getGlobal(shExports))) {
                        if (hasPathFallback(moduleName)) {
                            return;
                        } else {
                            return onError(makeError('nodefine',
                                             'No define call for ' + moduleName,
                                             null,
                                             [moduleName]));
                        }
                    } else {
                        //A script that does not call define(), so just simulate
                        //the call for it.
                        callGetModule([moduleName, (shim.deps || []), shim.exportsFn]);
                    }
                }

                checkLoaded();
            },

            /**
             * Converts a module name to a file path. Supports cases where
             * moduleName may actually be just an URL.
             * Note that it **does not** call normalize on the moduleName,
             * it is assumed to have already been normalized. This is an
             * internal API, not a public one. Use toUrl for the public API.
             */
            nameToUrl: function (moduleName, ext, skipExt) {
                var paths, syms, i, parentModule, url,
                    parentPath, bundleId,
                    pkgMain = getOwn(config.pkgs, moduleName);

                if (pkgMain) {
                    moduleName = pkgMain;
                }

                bundleId = getOwn(bundlesMap, moduleName);

                if (bundleId) {
                    return context.nameToUrl(bundleId, ext, skipExt);
                }

                //If a colon is in the URL, it indicates a protocol is used and it is just
                //an URL to a file, or if it starts with a slash, contains a query arg (i.e. ?)
                //or ends with .js, then assume the user meant to use an url and not a module id.
                //The slash is important for protocol-less URLs as well as full paths.
                if (req.jsExtRegExp.test(moduleName)) {
                    //Just a plain path, not module name lookup, so just return it.
                    //Add extension if it is included. This is a bit wonky, only non-.js things pass
                    //an extension, this method probably needs to be reworked.
                    url = moduleName + (ext || '');
                } else {
                    //A module that needs to be converted to a path.
                    paths = config.paths;

                    syms = moduleName.split('/');
                    //For each module name segment, see if there is a path
                    //registered for it. Start with most specific name
                    //and work up from it.
                    for (i = syms.length; i > 0; i -= 1) {
                        parentModule = syms.slice(0, i).join('/');

                        parentPath = getOwn(paths, parentModule);
                        if (parentPath) {
                            //If an array, it means there are a few choices,
                            //Choose the one that is desired
                            if (isArray(parentPath)) {
                                parentPath = parentPath[0];
                            }
                            syms.splice(0, i, parentPath);
                            break;
                        }
                    }

                    //Join the path parts together, then figure out if baseUrl is needed.
                    url = syms.join('/');
                    url += (ext || (/^data\:|\?/.test(url) || skipExt ? '' : '.js'));
                    url = (url.charAt(0) === '/' || url.match(/^[\w\+\.\-]+:/) ? '' : config.baseUrl) + url;
                }

                return config.urlArgs ? url +
                                        ((url.indexOf('?') === -1 ? '?' : '&') +
                                         config.urlArgs) : url;
            },

            //Delegates to req.load. Broken out as a separate function to
            //allow overriding in the optimizer.
            load: function (id, url) {
                req.load(context, id, url);
            },

            /**
             * Executes a module callback function. Broken out as a separate function
             * solely to allow the build system to sequence the files in the built
             * layer in the right sequence.
             *
             * @private
             */
            execCb: function (name, callback, args, exports) {
                return callback.apply(exports, args);
            },

            /**
             * callback for script loads, used to check status of loading.
             *
             * @param {Event} evt the event from the browser for the script
             * that was loaded.
             */
            onScriptLoad: function (evt) {
                //Using currentTarget instead of target for Firefox 2.0's sake. Not
                //all old browsers will be supported, but this one was easy enough
                //to support and still makes sense.
                if (evt.type === 'load' ||
                        (readyRegExp.test((evt.currentTarget || evt.srcElement).readyState))) {
                    //Reset interactive script so a script node is not held onto for
                    //to long.
                    interactiveScript = null;

                    //Pull out the name of the module and the context.
                    var data = getScriptData(evt);
                    context.completeLoad(data.id);
                }
            },

            /**
             * Callback for script errors.
             */
            onScriptError: function (evt) {
                var data = getScriptData(evt);
                if (!hasPathFallback(data.id)) {
                    return onError(makeError('scripterror', 'Script error for: ' + data.id, evt, [data.id]));
                }
            }
        };

        context.require = context.makeRequire();
        return context;
    }

    /**
     * Main entry point.
     *
     * If the only argument to require is a string, then the module that
     * is represented by that string is fetched for the appropriate context.
     *
     * If the first argument is an array, then it will be treated as an array
     * of dependency string names to fetch. An optional function callback can
     * be specified to execute when all of those dependencies are available.
     *
     * Make a local req variable to help Caja compliance (it assumes things
     * on a require that are not standardized), and to give a short
     * name for minification/local scope use.
     */
    req = requirejs = function (deps, callback, errback, optional) {

        //Find the right context, use default
        var context, config,
            contextName = defContextName;

        // Determine if have config object in the call.
        if (!isArray(deps) && typeof deps !== 'string') {
            // deps is a config object
            config = deps;
            if (isArray(callback)) {
                // Adjust args if there are dependencies
                deps = callback;
                callback = errback;
                errback = optional;
            } else {
                deps = [];
            }
        }

        if (config && config.context) {
            contextName = config.context;
        }

        context = getOwn(contexts, contextName);
        if (!context) {
            context = contexts[contextName] = req.s.newContext(contextName);
        }

        if (config) {
            context.configure(config);
        }

        return context.require(deps, callback, errback);
    };

    /**
     * Support require.config() to make it easier to cooperate with other
     * AMD loaders on globally agreed names.
     */
    req.config = function (config) {
        return req(config);
    };

    /**
     * Execute something after the current tick
     * of the event loop. Override for other envs
     * that have a better solution than setTimeout.
     * @param  {Function} fn function to execute later.
     */
    req.nextTick = typeof setTimeout !== 'undefined' ? function (fn) {
        setTimeout(fn, 4);
    } : function (fn) { fn(); };

    /**
     * Export require as a global, but only if it does not already exist.
     */
    if (!require) {
        require = req;
    }

    req.version = version;

    //Used to filter out dependencies that are already paths.
    req.jsExtRegExp = /^\/|:|\?|\.js$/;
    req.isBrowser = isBrowser;
    s = req.s = {
        contexts: contexts,
        newContext: newContext
    };

    //Create default context.
    req({});

    //Exports some context-sensitive methods on global require.
    each([
        'toUrl',
        'undef',
        'defined',
        'specified'
    ], function (prop) {
        //Reference from contexts instead of early binding to default context,
        //so that during builds, the latest instance of the default context
        //with its config gets used.
        req[prop] = function () {
            var ctx = contexts[defContextName];
            return ctx.require[prop].apply(ctx, arguments);
        };
    });

    if (isBrowser) {
        head = s.head = document.getElementsByTagName('head')[0];
        //If BASE tag is in play, using appendChild is a problem for IE6.
        //When that browser dies, this can be removed. Details in this jQuery bug:
        //http://dev.jquery.com/ticket/2709
        baseElement = document.getElementsByTagName('base')[0];
        if (baseElement) {
            head = s.head = baseElement.parentNode;
        }
    }

    /**
     * Any errors that require explicitly generates will be passed to this
     * function. Intercept/override it if you want custom error handling.
     * @param {Error} err the error object.
     */
    req.onError = defaultOnError;

    /**
     * Creates the node for the load command. Only used in browser envs.
     */
    req.createNode = function (config, moduleName, url) {
        var node = config.xhtml ?
                document.createElementNS('http://www.w3.org/1999/xhtml', 'html:script') :
                document.createElement('script');
        node.type = config.scriptType || 'text/javascript';
        node.charset = 'utf-8';
        node.async = true;
        return node;
    };

    /**
     * Does the request to load a module for the browser case.
     * Make this a separate function to allow other environments
     * to override it.
     *
     * @param {Object} context the require context to find state.
     * @param {String} moduleName the name of the module.
     * @param {Object} url the URL to the module.
     */
    req.load = function (context, moduleName, url) {
        var config = (context && context.config) || {},
            node;
        if (isBrowser) {
            //In the browser so use a script tag
            node = req.createNode(config, moduleName, url);

            node.setAttribute('data-requirecontext', context.contextName);
            node.setAttribute('data-requiremodule', moduleName);

            //Set up load listener. Test attachEvent first because IE9 has
            //a subtle issue in its addEventListener and script onload firings
            //that do not match the behavior of all other browsers with
            //addEventListener support, which fire the onload event for a
            //script right after the script execution. See:
            //https://connect.microsoft.com/IE/feedback/details/648057/script-onload-event-is-not-fired-immediately-after-script-execution
            //UNFORTUNATELY Opera implements attachEvent but does not follow the script
            //script execution mode.
            if (node.attachEvent &&
                    //Check if node.attachEvent is artificially added by custom script or
                    //natively supported by browser
                    //read https://github.com/jrburke/requirejs/issues/187
                    //if we can NOT find [native code] then it must NOT natively supported.
                    //in IE8, node.attachEvent does not have toString()
                    //Note the test for "[native code" with no closing brace, see:
                    //https://github.com/jrburke/requirejs/issues/273
                    !(node.attachEvent.toString && node.attachEvent.toString().indexOf('[native code') < 0) &&
                    !isOpera) {
                //Probably IE. IE (at least 6-8) do not fire
                //script onload right after executing the script, so
                //we cannot tie the anonymous define call to a name.
                //However, IE reports the script as being in 'interactive'
                //readyState at the time of the define call.
                useInteractive = true;

                node.attachEvent('onreadystatechange', context.onScriptLoad);
                //It would be great to add an error handler here to catch
                //404s in IE9+. However, onreadystatechange will fire before
                //the error handler, so that does not help. If addEventListener
                //is used, then IE will fire error before load, but we cannot
                //use that pathway given the connect.microsoft.com issue
                //mentioned above about not doing the 'script execute,
                //then fire the script load event listener before execute
                //next script' that other browsers do.
                //Best hope: IE10 fixes the issues,
                //and then destroys all installs of IE 6-9.
                //node.attachEvent('onerror', context.onScriptError);
            } else {
                node.addEventListener('load', context.onScriptLoad, false);
                node.addEventListener('error', context.onScriptError, false);
            }
            node.src = url;

            //For some cache cases in IE 6-8, the script executes before the end
            //of the appendChild execution, so to tie an anonymous define
            //call to the module name (which is stored on the node), hold on
            //to a reference to this node, but clear after the DOM insertion.
            currentlyAddingScript = node;
            if (baseElement) {
                head.insertBefore(node, baseElement);
            } else {
                head.appendChild(node);
            }
            currentlyAddingScript = null;

            return node;
        } else if (isWebWorker) {
            try {
                //In a web worker, use importScripts. This is not a very
                //efficient use of importScripts, importScripts will block until
                //its script is downloaded and evaluated. However, if web workers
                //are in play, the expectation that a build has been done so that
                //only one script needs to be loaded anyway. This may need to be
                //reevaluated if other use cases become common.
                importScripts(url);

                //Account for anonymous modules
                context.completeLoad(moduleName);
            } catch (e) {
                context.onError(makeError('importscripts',
                                'importScripts failed for ' +
                                    moduleName + ' at ' + url,
                                e,
                                [moduleName]));
            }
        }
    };

    function getInteractiveScript() {
        if (interactiveScript && interactiveScript.readyState === 'interactive') {
            return interactiveScript;
        }

        eachReverse(scripts(), function (script) {
            if (script.readyState === 'interactive') {
                return (interactiveScript = script);
            }
        });
        return interactiveScript;
    }

    //Look for a data-main script attribute, which could also adjust the baseUrl.
    if (isBrowser && !cfg.skipDataMain) {
        //Figure out baseUrl. Get it from the script tag with require.js in it.
        eachReverse(scripts(), function (script) {
            //Set the 'head' where we can append children by
            //using the script's parent.
            if (!head) {
                head = script.parentNode;
            }

            //Look for a data-main attribute to set main script for the page
            //to load. If it is there, the path to data main becomes the
            //baseUrl, if it is not already set.
            dataMain = script.getAttribute('data-main');
            if (dataMain) {
                //Preserve dataMain in case it is a path (i.e. contains '?')
                mainScript = dataMain;

                //Set final baseUrl if there is not already an explicit one.
                if (!cfg.baseUrl) {
                    //Pull off the directory of data-main for use as the
                    //baseUrl.
                    src = mainScript.split('/');
                    mainScript = src.pop();
                    subPath = src.length ? src.join('/')  + '/' : './';

                    cfg.baseUrl = subPath;
                }

                //Strip off any trailing .js since mainScript is now
                //like a module name.
                mainScript = mainScript.replace(jsSuffixRegExp, '');

                 //If mainScript is still a path, fall back to dataMain
                if (req.jsExtRegExp.test(mainScript)) {
                    mainScript = dataMain;
                }

                //Put the data-main script in the files to load.
                cfg.deps = cfg.deps ? cfg.deps.concat(mainScript) : [mainScript];

                return true;
            }
        });
    }

    /**
     * The function that handles definitions of modules. Differs from
     * require() in that a string for the module should be the first argument,
     * and the function to execute after dependencies are loaded should
     * return a value to define the module corresponding to the first argument's
     * name.
     */
    define = function (name, deps, callback) {
        var node, context;

        //Allow for anonymous modules
        if (typeof name !== 'string') {
            //Adjust args appropriately
            callback = deps;
            deps = name;
            name = null;
        }

        //This module may not have dependencies
        if (!isArray(deps)) {
            callback = deps;
            deps = null;
        }

        //If no name, and callback is a function, then figure out if it a
        //CommonJS thing with dependencies.
        if (!deps && isFunction(callback)) {
            deps = [];
            //Remove comments from the callback string,
            //look for require calls, and pull them into the dependencies,
            //but only if there are function args.
            if (callback.length) {
                callback
                    .toString()
                    .replace(commentRegExp, '')
                    .replace(cjsRequireRegExp, function (match, dep) {
                        deps.push(dep);
                    });

                //May be a CommonJS thing even without require calls, but still
                //could use exports, and module. Avoid doing exports and module
                //work though if it just needs require.
                //REQUIRES the function to expect the CommonJS variables in the
                //order listed below.
                deps = (callback.length === 1 ? ['require'] : ['require', 'exports', 'module']).concat(deps);
            }
        }

        //If in IE 6-8 and hit an anonymous define() call, do the interactive
        //work.
        if (useInteractive) {
            node = currentlyAddingScript || getInteractiveScript();
            if (node) {
                if (!name) {
                    name = node.getAttribute('data-requiremodule');
                }
                context = contexts[node.getAttribute('data-requirecontext')];
            }
        }

        //Always save off evaluating the def call until the script onload handler.
        //This allows multiple modules to be in a file without prematurely
        //tracing dependencies, and allows for anonymous module support,
        //where the module name is not known until the script onload event
        //occurs. If no context, use the global queue, and get it processed
        //in the onscript load callback.
        (context ? context.defQueue : globalDefQueue).push([name, deps, callback]);
    };

    define.amd = {
        jQuery: true
    };


    /**
     * Executes the text. Normally just uses eval, but can be modified
     * to use a better, environment-specific call. Only used for transpiling
     * loader plugins, not for plain JS modules.
     * @param {String} text the text to execute/evaluate.
     */
    req.exec = function (text) {
        /*jslint evil: true */
        return eval(text);
    };

    //Set up with config info.
    req(cfg);
}(this));

define("vendor/require", function(){});

/*!
 * jQuery JavaScript Library v1.11.1
 * http://jquery.com/
 *
 * Includes Sizzle.js
 * http://sizzlejs.com/
 *
 * Copyright 2005, 2014 jQuery Foundation, Inc. and other contributors
 * Released under the MIT license
 * http://jquery.org/license
 *
 * Date: 2014-05-01T17:42Z
 */


(function( global, factory ) {

	if ( typeof module === "object" && typeof module.exports === "object" ) {
		// For CommonJS and CommonJS-like environments where a proper window is present,
		// execute the factory and get jQuery
		// For environments that do not inherently posses a window with a document
		// (such as Node.js), expose a jQuery-making factory as module.exports
		// This accentuates the need for the creation of a real window
		// e.g. var jQuery = require("jquery")(window);
		// See ticket #14549 for more info
		module.exports = global.document ?
			factory( global, true ) :
			function( w ) {
				if ( !w.document ) {
					throw new Error( "jQuery requires a window with a document" );
				}
				return factory( w );
			};
	} else {
		factory( global );
	}

// Pass this if window is not defined yet
}(typeof window !== "undefined" ? window : this, function( window, noGlobal ) {

// Can't do this because several apps including ASP.NET trace
// the stack via arguments.caller.callee and Firefox dies if
// you try to trace through "use strict" call chains. (#13335)
// Support: Firefox 18+
//

var deletedIds = [];

var slice = deletedIds.slice;

var concat = deletedIds.concat;

var push = deletedIds.push;

var indexOf = deletedIds.indexOf;

var class2type = {};

var toString = class2type.toString;

var hasOwn = class2type.hasOwnProperty;

var support = {};



var
	version = "1.11.1",

	// Define a local copy of jQuery
	jQuery = function( selector, context ) {
		// The jQuery object is actually just the init constructor 'enhanced'
		// Need init if jQuery is called (just allow error to be thrown if not included)
		return new jQuery.fn.init( selector, context );
	},

	// Support: Android<4.1, IE<9
	// Make sure we trim BOM and NBSP
	rtrim = /^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g,

	// Matches dashed string for camelizing
	rmsPrefix = /^-ms-/,
	rdashAlpha = /-([\da-z])/gi,

	// Used by jQuery.camelCase as callback to replace()
	fcamelCase = function( all, letter ) {
		return letter.toUpperCase();
	};

jQuery.fn = jQuery.prototype = {
	// The current version of jQuery being used
	jquery: version,

	constructor: jQuery,

	// Start with an empty selector
	selector: "",

	// The default length of a jQuery object is 0
	length: 0,

	toArray: function() {
		return slice.call( this );
	},

	// Get the Nth element in the matched element set OR
	// Get the whole matched element set as a clean array
	get: function( num ) {
		return num != null ?

			// Return just the one element from the set
			( num < 0 ? this[ num + this.length ] : this[ num ] ) :

			// Return all the elements in a clean array
			slice.call( this );
	},

	// Take an array of elements and push it onto the stack
	// (returning the new matched element set)
	pushStack: function( elems ) {

		// Build a new jQuery matched element set
		var ret = jQuery.merge( this.constructor(), elems );

		// Add the old object onto the stack (as a reference)
		ret.prevObject = this;
		ret.context = this.context;

		// Return the newly-formed element set
		return ret;
	},

	// Execute a callback for every element in the matched set.
	// (You can seed the arguments with an array of args, but this is
	// only used internally.)
	each: function( callback, args ) {
		return jQuery.each( this, callback, args );
	},

	map: function( callback ) {
		return this.pushStack( jQuery.map(this, function( elem, i ) {
			return callback.call( elem, i, elem );
		}));
	},

	slice: function() {
		return this.pushStack( slice.apply( this, arguments ) );
	},

	first: function() {
		return this.eq( 0 );
	},

	last: function() {
		return this.eq( -1 );
	},

	eq: function( i ) {
		var len = this.length,
			j = +i + ( i < 0 ? len : 0 );
		return this.pushStack( j >= 0 && j < len ? [ this[j] ] : [] );
	},

	end: function() {
		return this.prevObject || this.constructor(null);
	},

	// For internal use only.
	// Behaves like an Array's method, not like a jQuery method.
	push: push,
	sort: deletedIds.sort,
	splice: deletedIds.splice
};

jQuery.extend = jQuery.fn.extend = function() {
	var src, copyIsArray, copy, name, options, clone,
		target = arguments[0] || {},
		i = 1,
		length = arguments.length,
		deep = false;

	// Handle a deep copy situation
	if ( typeof target === "boolean" ) {
		deep = target;

		// skip the boolean and the target
		target = arguments[ i ] || {};
		i++;
	}

	// Handle case when target is a string or something (possible in deep copy)
	if ( typeof target !== "object" && !jQuery.isFunction(target) ) {
		target = {};
	}

	// extend jQuery itself if only one argument is passed
	if ( i === length ) {
		target = this;
		i--;
	}

	for ( ; i < length; i++ ) {
		// Only deal with non-null/undefined values
		if ( (options = arguments[ i ]) != null ) {
			// Extend the base object
			for ( name in options ) {
				src = target[ name ];
				copy = options[ name ];

				// Prevent never-ending loop
				if ( target === copy ) {
					continue;
				}

				// Recurse if we're merging plain objects or arrays
				if ( deep && copy && ( jQuery.isPlainObject(copy) || (copyIsArray = jQuery.isArray(copy)) ) ) {
					if ( copyIsArray ) {
						copyIsArray = false;
						clone = src && jQuery.isArray(src) ? src : [];

					} else {
						clone = src && jQuery.isPlainObject(src) ? src : {};
					}

					// Never move original objects, clone them
					target[ name ] = jQuery.extend( deep, clone, copy );

				// Don't bring in undefined values
				} else if ( copy !== undefined ) {
					target[ name ] = copy;
				}
			}
		}
	}

	// Return the modified object
	return target;
};

jQuery.extend({
	// Unique for each copy of jQuery on the page
	expando: "jQuery" + ( version + Math.random() ).replace( /\D/g, "" ),

	// Assume jQuery is ready without the ready module
	isReady: true,

	error: function( msg ) {
		throw new Error( msg );
	},

	noop: function() {},

	// See test/unit/core.js for details concerning isFunction.
	// Since version 1.3, DOM methods and functions like alert
	// aren't supported. They return false on IE (#2968).
	isFunction: function( obj ) {
		return jQuery.type(obj) === "function";
	},

	isArray: Array.isArray || function( obj ) {
		return jQuery.type(obj) === "array";
	},

	isWindow: function( obj ) {
		/* jshint eqeqeq: false */
		return obj != null && obj == obj.window;
	},

	isNumeric: function( obj ) {
		// parseFloat NaNs numeric-cast false positives (null|true|false|"")
		// ...but misinterprets leading-number strings, particularly hex literals ("0x...")
		// subtraction forces infinities to NaN
		return !jQuery.isArray( obj ) && obj - parseFloat( obj ) >= 0;
	},

	isEmptyObject: function( obj ) {
		var name;
		for ( name in obj ) {
			return false;
		}
		return true;
	},

	isPlainObject: function( obj ) {
		var key;

		// Must be an Object.
		// Because of IE, we also have to check the presence of the constructor property.
		// Make sure that DOM nodes and window objects don't pass through, as well
		if ( !obj || jQuery.type(obj) !== "object" || obj.nodeType || jQuery.isWindow( obj ) ) {
			return false;
		}

		try {
			// Not own constructor property must be Object
			if ( obj.constructor &&
				!hasOwn.call(obj, "constructor") &&
				!hasOwn.call(obj.constructor.prototype, "isPrototypeOf") ) {
				return false;
			}
		} catch ( e ) {
			// IE8,9 Will throw exceptions on certain host objects #9897
			return false;
		}

		// Support: IE<9
		// Handle iteration over inherited properties before own properties.
		if ( support.ownLast ) {
			for ( key in obj ) {
				return hasOwn.call( obj, key );
			}
		}

		// Own properties are enumerated firstly, so to speed up,
		// if last one is own, then all properties are own.
		for ( key in obj ) {}

		return key === undefined || hasOwn.call( obj, key );
	},

	type: function( obj ) {
		if ( obj == null ) {
			return obj + "";
		}
		return typeof obj === "object" || typeof obj === "function" ?
			class2type[ toString.call(obj) ] || "object" :
			typeof obj;
	},

	// Evaluates a script in a global context
	// Workarounds based on findings by Jim Driscoll
	// http://weblogs.java.net/blog/driscoll/archive/2009/09/08/eval-javascript-global-context
	globalEval: function( data ) {
		if ( data && jQuery.trim( data ) ) {
			// We use execScript on Internet Explorer
			// We use an anonymous function so that context is window
			// rather than jQuery in Firefox
			( window.execScript || function( data ) {
				window[ "eval" ].call( window, data );
			} )( data );
		}
	},

	// Convert dashed to camelCase; used by the css and data modules
	// Microsoft forgot to hump their vendor prefix (#9572)
	camelCase: function( string ) {
		return string.replace( rmsPrefix, "ms-" ).replace( rdashAlpha, fcamelCase );
	},

	nodeName: function( elem, name ) {
		return elem.nodeName && elem.nodeName.toLowerCase() === name.toLowerCase();
	},

	// args is for internal usage only
	each: function( obj, callback, args ) {
		var value,
			i = 0,
			length = obj.length,
			isArray = isArraylike( obj );

		if ( args ) {
			if ( isArray ) {
				for ( ; i < length; i++ ) {
					value = callback.apply( obj[ i ], args );

					if ( value === false ) {
						break;
					}
				}
			} else {
				for ( i in obj ) {
					value = callback.apply( obj[ i ], args );

					if ( value === false ) {
						break;
					}
				}
			}

		// A special, fast, case for the most common use of each
		} else {
			if ( isArray ) {
				for ( ; i < length; i++ ) {
					value = callback.call( obj[ i ], i, obj[ i ] );

					if ( value === false ) {
						break;
					}
				}
			} else {
				for ( i in obj ) {
					value = callback.call( obj[ i ], i, obj[ i ] );

					if ( value === false ) {
						break;
					}
				}
			}
		}

		return obj;
	},

	// Support: Android<4.1, IE<9
	trim: function( text ) {
		return text == null ?
			"" :
			( text + "" ).replace( rtrim, "" );
	},

	// results is for internal usage only
	makeArray: function( arr, results ) {
		var ret = results || [];

		if ( arr != null ) {
			if ( isArraylike( Object(arr) ) ) {
				jQuery.merge( ret,
					typeof arr === "string" ?
					[ arr ] : arr
				);
			} else {
				push.call( ret, arr );
			}
		}

		return ret;
	},

	inArray: function( elem, arr, i ) {
		var len;

		if ( arr ) {
			if ( indexOf ) {
				return indexOf.call( arr, elem, i );
			}

			len = arr.length;
			i = i ? i < 0 ? Math.max( 0, len + i ) : i : 0;

			for ( ; i < len; i++ ) {
				// Skip accessing in sparse arrays
				if ( i in arr && arr[ i ] === elem ) {
					return i;
				}
			}
		}

		return -1;
	},

	merge: function( first, second ) {
		var len = +second.length,
			j = 0,
			i = first.length;

		while ( j < len ) {
			first[ i++ ] = second[ j++ ];
		}

		// Support: IE<9
		// Workaround casting of .length to NaN on otherwise arraylike objects (e.g., NodeLists)
		if ( len !== len ) {
			while ( second[j] !== undefined ) {
				first[ i++ ] = second[ j++ ];
			}
		}

		first.length = i;

		return first;
	},

	grep: function( elems, callback, invert ) {
		var callbackInverse,
			matches = [],
			i = 0,
			length = elems.length,
			callbackExpect = !invert;

		// Go through the array, only saving the items
		// that pass the validator function
		for ( ; i < length; i++ ) {
			callbackInverse = !callback( elems[ i ], i );
			if ( callbackInverse !== callbackExpect ) {
				matches.push( elems[ i ] );
			}
		}

		return matches;
	},

	// arg is for internal usage only
	map: function( elems, callback, arg ) {
		var value,
			i = 0,
			length = elems.length,
			isArray = isArraylike( elems ),
			ret = [];

		// Go through the array, translating each of the items to their new values
		if ( isArray ) {
			for ( ; i < length; i++ ) {
				value = callback( elems[ i ], i, arg );

				if ( value != null ) {
					ret.push( value );
				}
			}

		// Go through every key on the object,
		} else {
			for ( i in elems ) {
				value = callback( elems[ i ], i, arg );

				if ( value != null ) {
					ret.push( value );
				}
			}
		}

		// Flatten any nested arrays
		return concat.apply( [], ret );
	},

	// A global GUID counter for objects
	guid: 1,

	// Bind a function to a context, optionally partially applying any
	// arguments.
	proxy: function( fn, context ) {
		var args, proxy, tmp;

		if ( typeof context === "string" ) {
			tmp = fn[ context ];
			context = fn;
			fn = tmp;
		}

		// Quick check to determine if target is callable, in the spec
		// this throws a TypeError, but we will just return undefined.
		if ( !jQuery.isFunction( fn ) ) {
			return undefined;
		}

		// Simulated bind
		args = slice.call( arguments, 2 );
		proxy = function() {
			return fn.apply( context || this, args.concat( slice.call( arguments ) ) );
		};

		// Set the guid of unique handler to the same of original handler, so it can be removed
		proxy.guid = fn.guid = fn.guid || jQuery.guid++;

		return proxy;
	},

	now: function() {
		return +( new Date() );
	},

	// jQuery.support is not used in Core but other projects attach their
	// properties to it so it needs to exist.
	support: support
});

// Populate the class2type map
jQuery.each("Boolean Number String Function Array Date RegExp Object Error".split(" "), function(i, name) {
	class2type[ "[object " + name + "]" ] = name.toLowerCase();
});

function isArraylike( obj ) {
	var length = obj.length,
		type = jQuery.type( obj );

	if ( type === "function" || jQuery.isWindow( obj ) ) {
		return false;
	}

	if ( obj.nodeType === 1 && length ) {
		return true;
	}

	return type === "array" || length === 0 ||
		typeof length === "number" && length > 0 && ( length - 1 ) in obj;
}
var Sizzle =
/*!
 * Sizzle CSS Selector Engine v1.10.19
 * http://sizzlejs.com/
 *
 * Copyright 2013 jQuery Foundation, Inc. and other contributors
 * Released under the MIT license
 * http://jquery.org/license
 *
 * Date: 2014-04-18
 */
(function( window ) {

var i,
	support,
	Expr,
	getText,
	isXML,
	tokenize,
	compile,
	select,
	outermostContext,
	sortInput,
	hasDuplicate,

	// Local document vars
	setDocument,
	document,
	docElem,
	documentIsHTML,
	rbuggyQSA,
	rbuggyMatches,
	matches,
	contains,

	// Instance-specific data
	expando = "sizzle" + -(new Date()),
	preferredDoc = window.document,
	dirruns = 0,
	done = 0,
	classCache = createCache(),
	tokenCache = createCache(),
	compilerCache = createCache(),
	sortOrder = function( a, b ) {
		if ( a === b ) {
			hasDuplicate = true;
		}
		return 0;
	},

	// General-purpose constants
	strundefined = typeof undefined,
	MAX_NEGATIVE = 1 << 31,

	// Instance methods
	hasOwn = ({}).hasOwnProperty,
	arr = [],
	pop = arr.pop,
	push_native = arr.push,
	push = arr.push,
	slice = arr.slice,
	// Use a stripped-down indexOf if we can't use a native one
	indexOf = arr.indexOf || function( elem ) {
		var i = 0,
			len = this.length;
		for ( ; i < len; i++ ) {
			if ( this[i] === elem ) {
				return i;
			}
		}
		return -1;
	},

	booleans = "checked|selected|async|autofocus|autoplay|controls|defer|disabled|hidden|ismap|loop|multiple|open|readonly|required|scoped",

	// Regular expressions

	// Whitespace characters http://www.w3.org/TR/css3-selectors/#whitespace
	whitespace = "[\\x20\\t\\r\\n\\f]",
	// http://www.w3.org/TR/css3-syntax/#characters
	characterEncoding = "(?:\\\\.|[\\w-]|[^\\x00-\\xa0])+",

	// Loosely modeled on CSS identifier characters
	// An unquoted value should be a CSS identifier http://www.w3.org/TR/css3-selectors/#attribute-selectors
	// Proper syntax: http://www.w3.org/TR/CSS21/syndata.html#value-def-identifier
	identifier = characterEncoding.replace( "w", "w#" ),

	// Attribute selectors: http://www.w3.org/TR/selectors/#attribute-selectors
	attributes = "\\[" + whitespace + "*(" + characterEncoding + ")(?:" + whitespace +
		// Operator (capture 2)
		"*([*^$|!~]?=)" + whitespace +
		// "Attribute values must be CSS identifiers [capture 5] or strings [capture 3 or capture 4]"
		"*(?:'((?:\\\\.|[^\\\\'])*)'|\"((?:\\\\.|[^\\\\\"])*)\"|(" + identifier + "))|)" + whitespace +
		"*\\]",

	pseudos = ":(" + characterEncoding + ")(?:\\((" +
		// To reduce the number of selectors needing tokenize in the preFilter, prefer arguments:
		// 1. quoted (capture 3; capture 4 or capture 5)
		"('((?:\\\\.|[^\\\\'])*)'|\"((?:\\\\.|[^\\\\\"])*)\")|" +
		// 2. simple (capture 6)
		"((?:\\\\.|[^\\\\()[\\]]|" + attributes + ")*)|" +
		// 3. anything else (capture 2)
		".*" +
		")\\)|)",

	// Leading and non-escaped trailing whitespace, capturing some non-whitespace characters preceding the latter
	rtrim = new RegExp( "^" + whitespace + "+|((?:^|[^\\\\])(?:\\\\.)*)" + whitespace + "+$", "g" ),

	rcomma = new RegExp( "^" + whitespace + "*," + whitespace + "*" ),
	rcombinators = new RegExp( "^" + whitespace + "*([>+~]|" + whitespace + ")" + whitespace + "*" ),

	rattributeQuotes = new RegExp( "=" + whitespace + "*([^\\]'\"]*?)" + whitespace + "*\\]", "g" ),

	rpseudo = new RegExp( pseudos ),
	ridentifier = new RegExp( "^" + identifier + "$" ),

	matchExpr = {
		"ID": new RegExp( "^#(" + characterEncoding + ")" ),
		"CLASS": new RegExp( "^\\.(" + characterEncoding + ")" ),
		"TAG": new RegExp( "^(" + characterEncoding.replace( "w", "w*" ) + ")" ),
		"ATTR": new RegExp( "^" + attributes ),
		"PSEUDO": new RegExp( "^" + pseudos ),
		"CHILD": new RegExp( "^:(only|first|last|nth|nth-last)-(child|of-type)(?:\\(" + whitespace +
			"*(even|odd|(([+-]|)(\\d*)n|)" + whitespace + "*(?:([+-]|)" + whitespace +
			"*(\\d+)|))" + whitespace + "*\\)|)", "i" ),
		"bool": new RegExp( "^(?:" + booleans + ")$", "i" ),
		// For use in libraries implementing .is()
		// We use this for POS matching in `select`
		"needsContext": new RegExp( "^" + whitespace + "*[>+~]|:(even|odd|eq|gt|lt|nth|first|last)(?:\\(" +
			whitespace + "*((?:-\\d)?\\d*)" + whitespace + "*\\)|)(?=[^-]|$)", "i" )
	},

	rinputs = /^(?:input|select|textarea|button)$/i,
	rheader = /^h\d$/i,

	rnative = /^[^{]+\{\s*\[native \w/,

	// Easily-parseable/retrievable ID or TAG or CLASS selectors
	rquickExpr = /^(?:#([\w-]+)|(\w+)|\.([\w-]+))$/,

	rsibling = /[+~]/,
	rescape = /'|\\/g,

	// CSS escapes http://www.w3.org/TR/CSS21/syndata.html#escaped-characters
	runescape = new RegExp( "\\\\([\\da-f]{1,6}" + whitespace + "?|(" + whitespace + ")|.)", "ig" ),
	funescape = function( _, escaped, escapedWhitespace ) {
		var high = "0x" + escaped - 0x10000;
		// NaN means non-codepoint
		// Support: Firefox<24
		// Workaround erroneous numeric interpretation of +"0x"
		return high !== high || escapedWhitespace ?
			escaped :
			high < 0 ?
				// BMP codepoint
				String.fromCharCode( high + 0x10000 ) :
				// Supplemental Plane codepoint (surrogate pair)
				String.fromCharCode( high >> 10 | 0xD800, high & 0x3FF | 0xDC00 );
	};

// Optimize for push.apply( _, NodeList )
try {
	push.apply(
		(arr = slice.call( preferredDoc.childNodes )),
		preferredDoc.childNodes
	);
	// Support: Android<4.0
	// Detect silently failing push.apply
	arr[ preferredDoc.childNodes.length ].nodeType;
} catch ( e ) {
	push = { apply: arr.length ?

		// Leverage slice if possible
		function( target, els ) {
			push_native.apply( target, slice.call(els) );
		} :

		// Support: IE<9
		// Otherwise append directly
		function( target, els ) {
			var j = target.length,
				i = 0;
			// Can't trust NodeList.length
			while ( (target[j++] = els[i++]) ) {}
			target.length = j - 1;
		}
	};
}

function Sizzle( selector, context, results, seed ) {
	var match, elem, m, nodeType,
		// QSA vars
		i, groups, old, nid, newContext, newSelector;

	if ( ( context ? context.ownerDocument || context : preferredDoc ) !== document ) {
		setDocument( context );
	}

	context = context || document;
	results = results || [];

	if ( !selector || typeof selector !== "string" ) {
		return results;
	}

	if ( (nodeType = context.nodeType) !== 1 && nodeType !== 9 ) {
		return [];
	}

	if ( documentIsHTML && !seed ) {

		// Shortcuts
		if ( (match = rquickExpr.exec( selector )) ) {
			// Speed-up: Sizzle("#ID")
			if ( (m = match[1]) ) {
				if ( nodeType === 9 ) {
					elem = context.getElementById( m );
					// Check parentNode to catch when Blackberry 4.6 returns
					// nodes that are no longer in the document (jQuery #6963)
					if ( elem && elem.parentNode ) {
						// Handle the case where IE, Opera, and Webkit return items
						// by name instead of ID
						if ( elem.id === m ) {
							results.push( elem );
							return results;
						}
					} else {
						return results;
					}
				} else {
					// Context is not a document
					if ( context.ownerDocument && (elem = context.ownerDocument.getElementById( m )) &&
						contains( context, elem ) && elem.id === m ) {
						results.push( elem );
						return results;
					}
				}

			// Speed-up: Sizzle("TAG")
			} else if ( match[2] ) {
				push.apply( results, context.getElementsByTagName( selector ) );
				return results;

			// Speed-up: Sizzle(".CLASS")
			} else if ( (m = match[3]) && support.getElementsByClassName && context.getElementsByClassName ) {
				push.apply( results, context.getElementsByClassName( m ) );
				return results;
			}
		}

		// QSA path
		if ( support.qsa && (!rbuggyQSA || !rbuggyQSA.test( selector )) ) {
			nid = old = expando;
			newContext = context;
			newSelector = nodeType === 9 && selector;

			// qSA works strangely on Element-rooted queries
			// We can work around this by specifying an extra ID on the root
			// and working up from there (Thanks to Andrew Dupont for the technique)
			// IE 8 doesn't work on object elements
			if ( nodeType === 1 && context.nodeName.toLowerCase() !== "object" ) {
				groups = tokenize( selector );

				if ( (old = context.getAttribute("id")) ) {
					nid = old.replace( rescape, "\\$&" );
				} else {
					context.setAttribute( "id", nid );
				}
				nid = "[id='" + nid + "'] ";

				i = groups.length;
				while ( i-- ) {
					groups[i] = nid + toSelector( groups[i] );
				}
				newContext = rsibling.test( selector ) && testContext( context.parentNode ) || context;
				newSelector = groups.join(",");
			}

			if ( newSelector ) {
				try {
					push.apply( results,
						newContext.querySelectorAll( newSelector )
					);
					return results;
				} catch(qsaError) {
				} finally {
					if ( !old ) {
						context.removeAttribute("id");
					}
				}
			}
		}
	}

	// All others
	return select( selector.replace( rtrim, "$1" ), context, results, seed );
}

/**
 * Create key-value caches of limited size
 * @returns {Function(string, Object)} Returns the Object data after storing it on itself with
 *	property name the (space-suffixed) string and (if the cache is larger than Expr.cacheLength)
 *	deleting the oldest entry
 */
function createCache() {
	var keys = [];

	function cache( key, value ) {
		// Use (key + " ") to avoid collision with native prototype properties (see Issue #157)
		if ( keys.push( key + " " ) > Expr.cacheLength ) {
			// Only keep the most recent entries
			delete cache[ keys.shift() ];
		}
		return (cache[ key + " " ] = value);
	}
	return cache;
}

/**
 * Mark a function for special use by Sizzle
 * @param {Function} fn The function to mark
 */
function markFunction( fn ) {
	fn[ expando ] = true;
	return fn;
}

/**
 * Support testing using an element
 * @param {Function} fn Passed the created div and expects a boolean result
 */
function assert( fn ) {
	var div = document.createElement("div");

	try {
		return !!fn( div );
	} catch (e) {
		return false;
	} finally {
		// Remove from its parent by default
		if ( div.parentNode ) {
			div.parentNode.removeChild( div );
		}
		// release memory in IE
		div = null;
	}
}

/**
 * Adds the same handler for all of the specified attrs
 * @param {String} attrs Pipe-separated list of attributes
 * @param {Function} handler The method that will be applied
 */
function addHandle( attrs, handler ) {
	var arr = attrs.split("|"),
		i = attrs.length;

	while ( i-- ) {
		Expr.attrHandle[ arr[i] ] = handler;
	}
}

/**
 * Checks document order of two siblings
 * @param {Element} a
 * @param {Element} b
 * @returns {Number} Returns less than 0 if a precedes b, greater than 0 if a follows b
 */
function siblingCheck( a, b ) {
	var cur = b && a,
		diff = cur && a.nodeType === 1 && b.nodeType === 1 &&
			( ~b.sourceIndex || MAX_NEGATIVE ) -
			( ~a.sourceIndex || MAX_NEGATIVE );

	// Use IE sourceIndex if available on both nodes
	if ( diff ) {
		return diff;
	}

	// Check if b follows a
	if ( cur ) {
		while ( (cur = cur.nextSibling) ) {
			if ( cur === b ) {
				return -1;
			}
		}
	}

	return a ? 1 : -1;
}

/**
 * Returns a function to use in pseudos for input types
 * @param {String} type
 */
function createInputPseudo( type ) {
	return function( elem ) {
		var name = elem.nodeName.toLowerCase();
		return name === "input" && elem.type === type;
	};
}

/**
 * Returns a function to use in pseudos for buttons
 * @param {String} type
 */
function createButtonPseudo( type ) {
	return function( elem ) {
		var name = elem.nodeName.toLowerCase();
		return (name === "input" || name === "button") && elem.type === type;
	};
}

/**
 * Returns a function to use in pseudos for positionals
 * @param {Function} fn
 */
function createPositionalPseudo( fn ) {
	return markFunction(function( argument ) {
		argument = +argument;
		return markFunction(function( seed, matches ) {
			var j,
				matchIndexes = fn( [], seed.length, argument ),
				i = matchIndexes.length;

			// Match elements found at the specified indexes
			while ( i-- ) {
				if ( seed[ (j = matchIndexes[i]) ] ) {
					seed[j] = !(matches[j] = seed[j]);
				}
			}
		});
	});
}

/**
 * Checks a node for validity as a Sizzle context
 * @param {Element|Object=} context
 * @returns {Element|Object|Boolean} The input node if acceptable, otherwise a falsy value
 */
function testContext( context ) {
	return context && typeof context.getElementsByTagName !== strundefined && context;
}

// Expose support vars for convenience
support = Sizzle.support = {};

/**
 * Detects XML nodes
 * @param {Element|Object} elem An element or a document
 * @returns {Boolean} True iff elem is a non-HTML XML node
 */
isXML = Sizzle.isXML = function( elem ) {
	// documentElement is verified for cases where it doesn't yet exist
	// (such as loading iframes in IE - #4833)
	var documentElement = elem && (elem.ownerDocument || elem).documentElement;
	return documentElement ? documentElement.nodeName !== "HTML" : false;
};

/**
 * Sets document-related variables once based on the current document
 * @param {Element|Object} [doc] An element or document object to use to set the document
 * @returns {Object} Returns the current document
 */
setDocument = Sizzle.setDocument = function( node ) {
	var hasCompare,
		doc = node ? node.ownerDocument || node : preferredDoc,
		parent = doc.defaultView;

	// If no document and documentElement is available, return
	if ( doc === document || doc.nodeType !== 9 || !doc.documentElement ) {
		return document;
	}

	// Set our document
	document = doc;
	docElem = doc.documentElement;

	// Support tests
	documentIsHTML = !isXML( doc );

	// Support: IE>8
	// If iframe document is assigned to "document" variable and if iframe has been reloaded,
	// IE will throw "permission denied" error when accessing "document" variable, see jQuery #13936
	// IE6-8 do not support the defaultView property so parent will be undefined
	if ( parent && parent !== parent.top ) {
		// IE11 does not have attachEvent, so all must suffer
		if ( parent.addEventListener ) {
			parent.addEventListener( "unload", function() {
				setDocument();
			}, false );
		} else if ( parent.attachEvent ) {
			parent.attachEvent( "onunload", function() {
				setDocument();
			});
		}
	}

	/* Attributes
	---------------------------------------------------------------------- */

	// Support: IE<8
	// Verify that getAttribute really returns attributes and not properties (excepting IE8 booleans)
	support.attributes = assert(function( div ) {
		div.className = "i";
		return !div.getAttribute("className");
	});

	/* getElement(s)By*
	---------------------------------------------------------------------- */

	// Check if getElementsByTagName("*") returns only elements
	support.getElementsByTagName = assert(function( div ) {
		div.appendChild( doc.createComment("") );
		return !div.getElementsByTagName("*").length;
	});

	// Check if getElementsByClassName can be trusted
	support.getElementsByClassName = rnative.test( doc.getElementsByClassName ) && assert(function( div ) {
		div.innerHTML = "<div class='a'></div><div class='a i'></div>";

		// Support: Safari<4
		// Catch class over-caching
		div.firstChild.className = "i";
		// Support: Opera<10
		// Catch gEBCN failure to find non-leading classes
		return div.getElementsByClassName("i").length === 2;
	});

	// Support: IE<10
	// Check if getElementById returns elements by name
	// The broken getElementById methods don't pick up programatically-set names,
	// so use a roundabout getElementsByName test
	support.getById = assert(function( div ) {
		docElem.appendChild( div ).id = expando;
		return !doc.getElementsByName || !doc.getElementsByName( expando ).length;
	});

	// ID find and filter
	if ( support.getById ) {
		Expr.find["ID"] = function( id, context ) {
			if ( typeof context.getElementById !== strundefined && documentIsHTML ) {
				var m = context.getElementById( id );
				// Check parentNode to catch when Blackberry 4.6 returns
				// nodes that are no longer in the document #6963
				return m && m.parentNode ? [ m ] : [];
			}
		};
		Expr.filter["ID"] = function( id ) {
			var attrId = id.replace( runescape, funescape );
			return function( elem ) {
				return elem.getAttribute("id") === attrId;
			};
		};
	} else {
		// Support: IE6/7
		// getElementById is not reliable as a find shortcut
		delete Expr.find["ID"];

		Expr.filter["ID"] =  function( id ) {
			var attrId = id.replace( runescape, funescape );
			return function( elem ) {
				var node = typeof elem.getAttributeNode !== strundefined && elem.getAttributeNode("id");
				return node && node.value === attrId;
			};
		};
	}

	// Tag
	Expr.find["TAG"] = support.getElementsByTagName ?
		function( tag, context ) {
			if ( typeof context.getElementsByTagName !== strundefined ) {
				return context.getElementsByTagName( tag );
			}
		} :
		function( tag, context ) {
			var elem,
				tmp = [],
				i = 0,
				results = context.getElementsByTagName( tag );

			// Filter out possible comments
			if ( tag === "*" ) {
				while ( (elem = results[i++]) ) {
					if ( elem.nodeType === 1 ) {
						tmp.push( elem );
					}
				}

				return tmp;
			}
			return results;
		};

	// Class
	Expr.find["CLASS"] = support.getElementsByClassName && function( className, context ) {
		if ( typeof context.getElementsByClassName !== strundefined && documentIsHTML ) {
			return context.getElementsByClassName( className );
		}
	};

	/* QSA/matchesSelector
	---------------------------------------------------------------------- */

	// QSA and matchesSelector support

	// matchesSelector(:active) reports false when true (IE9/Opera 11.5)
	rbuggyMatches = [];

	// qSa(:focus) reports false when true (Chrome 21)
	// We allow this because of a bug in IE8/9 that throws an error
	// whenever `document.activeElement` is accessed on an iframe
	// So, we allow :focus to pass through QSA all the time to avoid the IE error
	// See http://bugs.jquery.com/ticket/13378
	rbuggyQSA = [];

	if ( (support.qsa = rnative.test( doc.querySelectorAll )) ) {
		// Build QSA regex
		// Regex strategy adopted from Diego Perini
		assert(function( div ) {
			// Select is set to empty string on purpose
			// This is to test IE's treatment of not explicitly
			// setting a boolean content attribute,
			// since its presence should be enough
			// http://bugs.jquery.com/ticket/12359
			div.innerHTML = "<select msallowclip=''><option selected=''></option></select>";

			// Support: IE8, Opera 11-12.16
			// Nothing should be selected when empty strings follow ^= or $= or *=
			// The test attribute must be unknown in Opera but "safe" for WinRT
			// http://msdn.microsoft.com/en-us/library/ie/hh465388.aspx#attribute_section
			if ( div.querySelectorAll("[msallowclip^='']").length ) {
				rbuggyQSA.push( "[*^$]=" + whitespace + "*(?:''|\"\")" );
			}

			// Support: IE8
			// Boolean attributes and "value" are not treated correctly
			if ( !div.querySelectorAll("[selected]").length ) {
				rbuggyQSA.push( "\\[" + whitespace + "*(?:value|" + booleans + ")" );
			}

			// Webkit/Opera - :checked should return selected option elements
			// http://www.w3.org/TR/2011/REC-css3-selectors-20110929/#checked
			// IE8 throws error here and will not see later tests
			if ( !div.querySelectorAll(":checked").length ) {
				rbuggyQSA.push(":checked");
			}
		});

		assert(function( div ) {
			// Support: Windows 8 Native Apps
			// The type and name attributes are restricted during .innerHTML assignment
			var input = doc.createElement("input");
			input.setAttribute( "type", "hidden" );
			div.appendChild( input ).setAttribute( "name", "D" );

			// Support: IE8
			// Enforce case-sensitivity of name attribute
			if ( div.querySelectorAll("[name=d]").length ) {
				rbuggyQSA.push( "name" + whitespace + "*[*^$|!~]?=" );
			}

			// FF 3.5 - :enabled/:disabled and hidden elements (hidden elements are still enabled)
			// IE8 throws error here and will not see later tests
			if ( !div.querySelectorAll(":enabled").length ) {
				rbuggyQSA.push( ":enabled", ":disabled" );
			}

			// Opera 10-11 does not throw on post-comma invalid pseudos
			div.querySelectorAll("*,:x");
			rbuggyQSA.push(",.*:");
		});
	}

	if ( (support.matchesSelector = rnative.test( (matches = docElem.matches ||
		docElem.webkitMatchesSelector ||
		docElem.mozMatchesSelector ||
		docElem.oMatchesSelector ||
		docElem.msMatchesSelector) )) ) {

		assert(function( div ) {
			// Check to see if it's possible to do matchesSelector
			// on a disconnected node (IE 9)
			support.disconnectedMatch = matches.call( div, "div" );

			// This should fail with an exception
			// Gecko does not error, returns false instead
			matches.call( div, "[s!='']:x" );
			rbuggyMatches.push( "!=", pseudos );
		});
	}

	rbuggyQSA = rbuggyQSA.length && new RegExp( rbuggyQSA.join("|") );
	rbuggyMatches = rbuggyMatches.length && new RegExp( rbuggyMatches.join("|") );

	/* Contains
	---------------------------------------------------------------------- */
	hasCompare = rnative.test( docElem.compareDocumentPosition );

	// Element contains another
	// Purposefully does not implement inclusive descendent
	// As in, an element does not contain itself
	contains = hasCompare || rnative.test( docElem.contains ) ?
		function( a, b ) {
			var adown = a.nodeType === 9 ? a.documentElement : a,
				bup = b && b.parentNode;
			return a === bup || !!( bup && bup.nodeType === 1 && (
				adown.contains ?
					adown.contains( bup ) :
					a.compareDocumentPosition && a.compareDocumentPosition( bup ) & 16
			));
		} :
		function( a, b ) {
			if ( b ) {
				while ( (b = b.parentNode) ) {
					if ( b === a ) {
						return true;
					}
				}
			}
			return false;
		};

	/* Sorting
	---------------------------------------------------------------------- */

	// Document order sorting
	sortOrder = hasCompare ?
	function( a, b ) {

		// Flag for duplicate removal
		if ( a === b ) {
			hasDuplicate = true;
			return 0;
		}

		// Sort on method existence if only one input has compareDocumentPosition
		var compare = !a.compareDocumentPosition - !b.compareDocumentPosition;
		if ( compare ) {
			return compare;
		}

		// Calculate position if both inputs belong to the same document
		compare = ( a.ownerDocument || a ) === ( b.ownerDocument || b ) ?
			a.compareDocumentPosition( b ) :

			// Otherwise we know they are disconnected
			1;

		// Disconnected nodes
		if ( compare & 1 ||
			(!support.sortDetached && b.compareDocumentPosition( a ) === compare) ) {

			// Choose the first element that is related to our preferred document
			if ( a === doc || a.ownerDocument === preferredDoc && contains(preferredDoc, a) ) {
				return -1;
			}
			if ( b === doc || b.ownerDocument === preferredDoc && contains(preferredDoc, b) ) {
				return 1;
			}

			// Maintain original order
			return sortInput ?
				( indexOf.call( sortInput, a ) - indexOf.call( sortInput, b ) ) :
				0;
		}

		return compare & 4 ? -1 : 1;
	} :
	function( a, b ) {
		// Exit early if the nodes are identical
		if ( a === b ) {
			hasDuplicate = true;
			return 0;
		}

		var cur,
			i = 0,
			aup = a.parentNode,
			bup = b.parentNode,
			ap = [ a ],
			bp = [ b ];

		// Parentless nodes are either documents or disconnected
		if ( !aup || !bup ) {
			return a === doc ? -1 :
				b === doc ? 1 :
				aup ? -1 :
				bup ? 1 :
				sortInput ?
				( indexOf.call( sortInput, a ) - indexOf.call( sortInput, b ) ) :
				0;

		// If the nodes are siblings, we can do a quick check
		} else if ( aup === bup ) {
			return siblingCheck( a, b );
		}

		// Otherwise we need full lists of their ancestors for comparison
		cur = a;
		while ( (cur = cur.parentNode) ) {
			ap.unshift( cur );
		}
		cur = b;
		while ( (cur = cur.parentNode) ) {
			bp.unshift( cur );
		}

		// Walk down the tree looking for a discrepancy
		while ( ap[i] === bp[i] ) {
			i++;
		}

		return i ?
			// Do a sibling check if the nodes have a common ancestor
			siblingCheck( ap[i], bp[i] ) :

			// Otherwise nodes in our document sort first
			ap[i] === preferredDoc ? -1 :
			bp[i] === preferredDoc ? 1 :
			0;
	};

	return doc;
};

Sizzle.matches = function( expr, elements ) {
	return Sizzle( expr, null, null, elements );
};

Sizzle.matchesSelector = function( elem, expr ) {
	// Set document vars if needed
	if ( ( elem.ownerDocument || elem ) !== document ) {
		setDocument( elem );
	}

	// Make sure that attribute selectors are quoted
	expr = expr.replace( rattributeQuotes, "='$1']" );

	if ( support.matchesSelector && documentIsHTML &&
		( !rbuggyMatches || !rbuggyMatches.test( expr ) ) &&
		( !rbuggyQSA     || !rbuggyQSA.test( expr ) ) ) {

		try {
			var ret = matches.call( elem, expr );

			// IE 9's matchesSelector returns false on disconnected nodes
			if ( ret || support.disconnectedMatch ||
					// As well, disconnected nodes are said to be in a document
					// fragment in IE 9
					elem.document && elem.document.nodeType !== 11 ) {
				return ret;
			}
		} catch(e) {}
	}

	return Sizzle( expr, document, null, [ elem ] ).length > 0;
};

Sizzle.contains = function( context, elem ) {
	// Set document vars if needed
	if ( ( context.ownerDocument || context ) !== document ) {
		setDocument( context );
	}
	return contains( context, elem );
};

Sizzle.attr = function( elem, name ) {
	// Set document vars if needed
	if ( ( elem.ownerDocument || elem ) !== document ) {
		setDocument( elem );
	}

	var fn = Expr.attrHandle[ name.toLowerCase() ],
		// Don't get fooled by Object.prototype properties (jQuery #13807)
		val = fn && hasOwn.call( Expr.attrHandle, name.toLowerCase() ) ?
			fn( elem, name, !documentIsHTML ) :
			undefined;

	return val !== undefined ?
		val :
		support.attributes || !documentIsHTML ?
			elem.getAttribute( name ) :
			(val = elem.getAttributeNode(name)) && val.specified ?
				val.value :
				null;
};

Sizzle.error = function( msg ) {
	throw new Error( "Syntax error, unrecognized expression: " + msg );
};

/**
 * Document sorting and removing duplicates
 * @param {ArrayLike} results
 */
Sizzle.uniqueSort = function( results ) {
	var elem,
		duplicates = [],
		j = 0,
		i = 0;

	// Unless we *know* we can detect duplicates, assume their presence
	hasDuplicate = !support.detectDuplicates;
	sortInput = !support.sortStable && results.slice( 0 );
	results.sort( sortOrder );

	if ( hasDuplicate ) {
		while ( (elem = results[i++]) ) {
			if ( elem === results[ i ] ) {
				j = duplicates.push( i );
			}
		}
		while ( j-- ) {
			results.splice( duplicates[ j ], 1 );
		}
	}

	// Clear input after sorting to release objects
	// See https://github.com/jquery/sizzle/pull/225
	sortInput = null;

	return results;
};

/**
 * Utility function for retrieving the text value of an array of DOM nodes
 * @param {Array|Element} elem
 */
getText = Sizzle.getText = function( elem ) {
	var node,
		ret = "",
		i = 0,
		nodeType = elem.nodeType;

	if ( !nodeType ) {
		// If no nodeType, this is expected to be an array
		while ( (node = elem[i++]) ) {
			// Do not traverse comment nodes
			ret += getText( node );
		}
	} else if ( nodeType === 1 || nodeType === 9 || nodeType === 11 ) {
		// Use textContent for elements
		// innerText usage removed for consistency of new lines (jQuery #11153)
		if ( typeof elem.textContent === "string" ) {
			return elem.textContent;
		} else {
			// Traverse its children
			for ( elem = elem.firstChild; elem; elem = elem.nextSibling ) {
				ret += getText( elem );
			}
		}
	} else if ( nodeType === 3 || nodeType === 4 ) {
		return elem.nodeValue;
	}
	// Do not include comment or processing instruction nodes

	return ret;
};

Expr = Sizzle.selectors = {

	// Can be adjusted by the user
	cacheLength: 50,

	createPseudo: markFunction,

	match: matchExpr,

	attrHandle: {},

	find: {},

	relative: {
		">": { dir: "parentNode", first: true },
		" ": { dir: "parentNode" },
		"+": { dir: "previousSibling", first: true },
		"~": { dir: "previousSibling" }
	},

	preFilter: {
		"ATTR": function( match ) {
			match[1] = match[1].replace( runescape, funescape );

			// Move the given value to match[3] whether quoted or unquoted
			match[3] = ( match[3] || match[4] || match[5] || "" ).replace( runescape, funescape );

			if ( match[2] === "~=" ) {
				match[3] = " " + match[3] + " ";
			}

			return match.slice( 0, 4 );
		},

		"CHILD": function( match ) {
			/* matches from matchExpr["CHILD"]
				1 type (only|nth|...)
				2 what (child|of-type)
				3 argument (even|odd|\d*|\d*n([+-]\d+)?|...)
				4 xn-component of xn+y argument ([+-]?\d*n|)
				5 sign of xn-component
				6 x of xn-component
				7 sign of y-component
				8 y of y-component
			*/
			match[1] = match[1].toLowerCase();

			if ( match[1].slice( 0, 3 ) === "nth" ) {
				// nth-* requires argument
				if ( !match[3] ) {
					Sizzle.error( match[0] );
				}

				// numeric x and y parameters for Expr.filter.CHILD
				// remember that false/true cast respectively to 0/1
				match[4] = +( match[4] ? match[5] + (match[6] || 1) : 2 * ( match[3] === "even" || match[3] === "odd" ) );
				match[5] = +( ( match[7] + match[8] ) || match[3] === "odd" );

			// other types prohibit arguments
			} else if ( match[3] ) {
				Sizzle.error( match[0] );
			}

			return match;
		},

		"PSEUDO": function( match ) {
			var excess,
				unquoted = !match[6] && match[2];

			if ( matchExpr["CHILD"].test( match[0] ) ) {
				return null;
			}

			// Accept quoted arguments as-is
			if ( match[3] ) {
				match[2] = match[4] || match[5] || "";

			// Strip excess characters from unquoted arguments
			} else if ( unquoted && rpseudo.test( unquoted ) &&
				// Get excess from tokenize (recursively)
				(excess = tokenize( unquoted, true )) &&
				// advance to the next closing parenthesis
				(excess = unquoted.indexOf( ")", unquoted.length - excess ) - unquoted.length) ) {

				// excess is a negative index
				match[0] = match[0].slice( 0, excess );
				match[2] = unquoted.slice( 0, excess );
			}

			// Return only captures needed by the pseudo filter method (type and argument)
			return match.slice( 0, 3 );
		}
	},

	filter: {

		"TAG": function( nodeNameSelector ) {
			var nodeName = nodeNameSelector.replace( runescape, funescape ).toLowerCase();
			return nodeNameSelector === "*" ?
				function() { return true; } :
				function( elem ) {
					return elem.nodeName && elem.nodeName.toLowerCase() === nodeName;
				};
		},

		"CLASS": function( className ) {
			var pattern = classCache[ className + " " ];

			return pattern ||
				(pattern = new RegExp( "(^|" + whitespace + ")" + className + "(" + whitespace + "|$)" )) &&
				classCache( className, function( elem ) {
					return pattern.test( typeof elem.className === "string" && elem.className || typeof elem.getAttribute !== strundefined && elem.getAttribute("class") || "" );
				});
		},

		"ATTR": function( name, operator, check ) {
			return function( elem ) {
				var result = Sizzle.attr( elem, name );

				if ( result == null ) {
					return operator === "!=";
				}
				if ( !operator ) {
					return true;
				}

				result += "";

				return operator === "=" ? result === check :
					operator === "!=" ? result !== check :
					operator === "^=" ? check && result.indexOf( check ) === 0 :
					operator === "*=" ? check && result.indexOf( check ) > -1 :
					operator === "$=" ? check && result.slice( -check.length ) === check :
					operator === "~=" ? ( " " + result + " " ).indexOf( check ) > -1 :
					operator === "|=" ? result === check || result.slice( 0, check.length + 1 ) === check + "-" :
					false;
			};
		},

		"CHILD": function( type, what, argument, first, last ) {
			var simple = type.slice( 0, 3 ) !== "nth",
				forward = type.slice( -4 ) !== "last",
				ofType = what === "of-type";

			return first === 1 && last === 0 ?

				// Shortcut for :nth-*(n)
				function( elem ) {
					return !!elem.parentNode;
				} :

				function( elem, context, xml ) {
					var cache, outerCache, node, diff, nodeIndex, start,
						dir = simple !== forward ? "nextSibling" : "previousSibling",
						parent = elem.parentNode,
						name = ofType && elem.nodeName.toLowerCase(),
						useCache = !xml && !ofType;

					if ( parent ) {

						// :(first|last|only)-(child|of-type)
						if ( simple ) {
							while ( dir ) {
								node = elem;
								while ( (node = node[ dir ]) ) {
									if ( ofType ? node.nodeName.toLowerCase() === name : node.nodeType === 1 ) {
										return false;
									}
								}
								// Reverse direction for :only-* (if we haven't yet done so)
								start = dir = type === "only" && !start && "nextSibling";
							}
							return true;
						}

						start = [ forward ? parent.firstChild : parent.lastChild ];

						// non-xml :nth-child(...) stores cache data on `parent`
						if ( forward && useCache ) {
							// Seek `elem` from a previously-cached index
							outerCache = parent[ expando ] || (parent[ expando ] = {});
							cache = outerCache[ type ] || [];
							nodeIndex = cache[0] === dirruns && cache[1];
							diff = cache[0] === dirruns && cache[2];
							node = nodeIndex && parent.childNodes[ nodeIndex ];

							while ( (node = ++nodeIndex && node && node[ dir ] ||

								// Fallback to seeking `elem` from the start
								(diff = nodeIndex = 0) || start.pop()) ) {

								// When found, cache indexes on `parent` and break
								if ( node.nodeType === 1 && ++diff && node === elem ) {
									outerCache[ type ] = [ dirruns, nodeIndex, diff ];
									break;
								}
							}

						// Use previously-cached element index if available
						} else if ( useCache && (cache = (elem[ expando ] || (elem[ expando ] = {}))[ type ]) && cache[0] === dirruns ) {
							diff = cache[1];

						// xml :nth-child(...) or :nth-last-child(...) or :nth(-last)?-of-type(...)
						} else {
							// Use the same loop as above to seek `elem` from the start
							while ( (node = ++nodeIndex && node && node[ dir ] ||
								(diff = nodeIndex = 0) || start.pop()) ) {

								if ( ( ofType ? node.nodeName.toLowerCase() === name : node.nodeType === 1 ) && ++diff ) {
									// Cache the index of each encountered element
									if ( useCache ) {
										(node[ expando ] || (node[ expando ] = {}))[ type ] = [ dirruns, diff ];
									}

									if ( node === elem ) {
										break;
									}
								}
							}
						}

						// Incorporate the offset, then check against cycle size
						diff -= last;
						return diff === first || ( diff % first === 0 && diff / first >= 0 );
					}
				};
		},

		"PSEUDO": function( pseudo, argument ) {
			// pseudo-class names are case-insensitive
			// http://www.w3.org/TR/selectors/#pseudo-classes
			// Prioritize by case sensitivity in case custom pseudos are added with uppercase letters
			// Remember that setFilters inherits from pseudos
			var args,
				fn = Expr.pseudos[ pseudo ] || Expr.setFilters[ pseudo.toLowerCase() ] ||
					Sizzle.error( "unsupported pseudo: " + pseudo );

			// The user may use createPseudo to indicate that
			// arguments are needed to create the filter function
			// just as Sizzle does
			if ( fn[ expando ] ) {
				return fn( argument );
			}

			// But maintain support for old signatures
			if ( fn.length > 1 ) {
				args = [ pseudo, pseudo, "", argument ];
				return Expr.setFilters.hasOwnProperty( pseudo.toLowerCase() ) ?
					markFunction(function( seed, matches ) {
						var idx,
							matched = fn( seed, argument ),
							i = matched.length;
						while ( i-- ) {
							idx = indexOf.call( seed, matched[i] );
							seed[ idx ] = !( matches[ idx ] = matched[i] );
						}
					}) :
					function( elem ) {
						return fn( elem, 0, args );
					};
			}

			return fn;
		}
	},

	pseudos: {
		// Potentially complex pseudos
		"not": markFunction(function( selector ) {
			// Trim the selector passed to compile
			// to avoid treating leading and trailing
			// spaces as combinators
			var input = [],
				results = [],
				matcher = compile( selector.replace( rtrim, "$1" ) );

			return matcher[ expando ] ?
				markFunction(function( seed, matches, context, xml ) {
					var elem,
						unmatched = matcher( seed, null, xml, [] ),
						i = seed.length;

					// Match elements unmatched by `matcher`
					while ( i-- ) {
						if ( (elem = unmatched[i]) ) {
							seed[i] = !(matches[i] = elem);
						}
					}
				}) :
				function( elem, context, xml ) {
					input[0] = elem;
					matcher( input, null, xml, results );
					return !results.pop();
				};
		}),

		"has": markFunction(function( selector ) {
			return function( elem ) {
				return Sizzle( selector, elem ).length > 0;
			};
		}),

		"contains": markFunction(function( text ) {
			return function( elem ) {
				return ( elem.textContent || elem.innerText || getText( elem ) ).indexOf( text ) > -1;
			};
		}),

		// "Whether an element is represented by a :lang() selector
		// is based solely on the element's language value
		// being equal to the identifier C,
		// or beginning with the identifier C immediately followed by "-".
		// The matching of C against the element's language value is performed case-insensitively.
		// The identifier C does not have to be a valid language name."
		// http://www.w3.org/TR/selectors/#lang-pseudo
		"lang": markFunction( function( lang ) {
			// lang value must be a valid identifier
			if ( !ridentifier.test(lang || "") ) {
				Sizzle.error( "unsupported lang: " + lang );
			}
			lang = lang.replace( runescape, funescape ).toLowerCase();
			return function( elem ) {
				var elemLang;
				do {
					if ( (elemLang = documentIsHTML ?
						elem.lang :
						elem.getAttribute("xml:lang") || elem.getAttribute("lang")) ) {

						elemLang = elemLang.toLowerCase();
						return elemLang === lang || elemLang.indexOf( lang + "-" ) === 0;
					}
				} while ( (elem = elem.parentNode) && elem.nodeType === 1 );
				return false;
			};
		}),

		// Miscellaneous
		"target": function( elem ) {
			var hash = window.location && window.location.hash;
			return hash && hash.slice( 1 ) === elem.id;
		},

		"root": function( elem ) {
			return elem === docElem;
		},

		"focus": function( elem ) {
			return elem === document.activeElement && (!document.hasFocus || document.hasFocus()) && !!(elem.type || elem.href || ~elem.tabIndex);
		},

		// Boolean properties
		"enabled": function( elem ) {
			return elem.disabled === false;
		},

		"disabled": function( elem ) {
			return elem.disabled === true;
		},

		"checked": function( elem ) {
			// In CSS3, :checked should return both checked and selected elements
			// http://www.w3.org/TR/2011/REC-css3-selectors-20110929/#checked
			var nodeName = elem.nodeName.toLowerCase();
			return (nodeName === "input" && !!elem.checked) || (nodeName === "option" && !!elem.selected);
		},

		"selected": function( elem ) {
			// Accessing this property makes selected-by-default
			// options in Safari work properly
			if ( elem.parentNode ) {
				elem.parentNode.selectedIndex;
			}

			return elem.selected === true;
		},

		// Contents
		"empty": function( elem ) {
			// http://www.w3.org/TR/selectors/#empty-pseudo
			// :empty is negated by element (1) or content nodes (text: 3; cdata: 4; entity ref: 5),
			//   but not by others (comment: 8; processing instruction: 7; etc.)
			// nodeType < 6 works because attributes (2) do not appear as children
			for ( elem = elem.firstChild; elem; elem = elem.nextSibling ) {
				if ( elem.nodeType < 6 ) {
					return false;
				}
			}
			return true;
		},

		"parent": function( elem ) {
			return !Expr.pseudos["empty"]( elem );
		},

		// Element/input types
		"header": function( elem ) {
			return rheader.test( elem.nodeName );
		},

		"input": function( elem ) {
			return rinputs.test( elem.nodeName );
		},

		"button": function( elem ) {
			var name = elem.nodeName.toLowerCase();
			return name === "input" && elem.type === "button" || name === "button";
		},

		"text": function( elem ) {
			var attr;
			return elem.nodeName.toLowerCase() === "input" &&
				elem.type === "text" &&

				// Support: IE<8
				// New HTML5 attribute values (e.g., "search") appear with elem.type === "text"
				( (attr = elem.getAttribute("type")) == null || attr.toLowerCase() === "text" );
		},

		// Position-in-collection
		"first": createPositionalPseudo(function() {
			return [ 0 ];
		}),

		"last": createPositionalPseudo(function( matchIndexes, length ) {
			return [ length - 1 ];
		}),

		"eq": createPositionalPseudo(function( matchIndexes, length, argument ) {
			return [ argument < 0 ? argument + length : argument ];
		}),

		"even": createPositionalPseudo(function( matchIndexes, length ) {
			var i = 0;
			for ( ; i < length; i += 2 ) {
				matchIndexes.push( i );
			}
			return matchIndexes;
		}),

		"odd": createPositionalPseudo(function( matchIndexes, length ) {
			var i = 1;
			for ( ; i < length; i += 2 ) {
				matchIndexes.push( i );
			}
			return matchIndexes;
		}),

		"lt": createPositionalPseudo(function( matchIndexes, length, argument ) {
			var i = argument < 0 ? argument + length : argument;
			for ( ; --i >= 0; ) {
				matchIndexes.push( i );
			}
			return matchIndexes;
		}),

		"gt": createPositionalPseudo(function( matchIndexes, length, argument ) {
			var i = argument < 0 ? argument + length : argument;
			for ( ; ++i < length; ) {
				matchIndexes.push( i );
			}
			return matchIndexes;
		})
	}
};

Expr.pseudos["nth"] = Expr.pseudos["eq"];

// Add button/input type pseudos
for ( i in { radio: true, checkbox: true, file: true, password: true, image: true } ) {
	Expr.pseudos[ i ] = createInputPseudo( i );
}
for ( i in { submit: true, reset: true } ) {
	Expr.pseudos[ i ] = createButtonPseudo( i );
}

// Easy API for creating new setFilters
function setFilters() {}
setFilters.prototype = Expr.filters = Expr.pseudos;
Expr.setFilters = new setFilters();

tokenize = Sizzle.tokenize = function( selector, parseOnly ) {
	var matched, match, tokens, type,
		soFar, groups, preFilters,
		cached = tokenCache[ selector + " " ];

	if ( cached ) {
		return parseOnly ? 0 : cached.slice( 0 );
	}

	soFar = selector;
	groups = [];
	preFilters = Expr.preFilter;

	while ( soFar ) {

		// Comma and first run
		if ( !matched || (match = rcomma.exec( soFar )) ) {
			if ( match ) {
				// Don't consume trailing commas as valid
				soFar = soFar.slice( match[0].length ) || soFar;
			}
			groups.push( (tokens = []) );
		}

		matched = false;

		// Combinators
		if ( (match = rcombinators.exec( soFar )) ) {
			matched = match.shift();
			tokens.push({
				value: matched,
				// Cast descendant combinators to space
				type: match[0].replace( rtrim, " " )
			});
			soFar = soFar.slice( matched.length );
		}

		// Filters
		for ( type in Expr.filter ) {
			if ( (match = matchExpr[ type ].exec( soFar )) && (!preFilters[ type ] ||
				(match = preFilters[ type ]( match ))) ) {
				matched = match.shift();
				tokens.push({
					value: matched,
					type: type,
					matches: match
				});
				soFar = soFar.slice( matched.length );
			}
		}

		if ( !matched ) {
			break;
		}
	}

	// Return the length of the invalid excess
	// if we're just parsing
	// Otherwise, throw an error or return tokens
	return parseOnly ?
		soFar.length :
		soFar ?
			Sizzle.error( selector ) :
			// Cache the tokens
			tokenCache( selector, groups ).slice( 0 );
};

function toSelector( tokens ) {
	var i = 0,
		len = tokens.length,
		selector = "";
	for ( ; i < len; i++ ) {
		selector += tokens[i].value;
	}
	return selector;
}

function addCombinator( matcher, combinator, base ) {
	var dir = combinator.dir,
		checkNonElements = base && dir === "parentNode",
		doneName = done++;

	return combinator.first ?
		// Check against closest ancestor/preceding element
		function( elem, context, xml ) {
			while ( (elem = elem[ dir ]) ) {
				if ( elem.nodeType === 1 || checkNonElements ) {
					return matcher( elem, context, xml );
				}
			}
		} :

		// Check against all ancestor/preceding elements
		function( elem, context, xml ) {
			var oldCache, outerCache,
				newCache = [ dirruns, doneName ];

			// We can't set arbitrary data on XML nodes, so they don't benefit from dir caching
			if ( xml ) {
				while ( (elem = elem[ dir ]) ) {
					if ( elem.nodeType === 1 || checkNonElements ) {
						if ( matcher( elem, context, xml ) ) {
							return true;
						}
					}
				}
			} else {
				while ( (elem = elem[ dir ]) ) {
					if ( elem.nodeType === 1 || checkNonElements ) {
						outerCache = elem[ expando ] || (elem[ expando ] = {});
						if ( (oldCache = outerCache[ dir ]) &&
							oldCache[ 0 ] === dirruns && oldCache[ 1 ] === doneName ) {

							// Assign to newCache so results back-propagate to previous elements
							return (newCache[ 2 ] = oldCache[ 2 ]);
						} else {
							// Reuse newcache so results back-propagate to previous elements
							outerCache[ dir ] = newCache;

							// A match means we're done; a fail means we have to keep checking
							if ( (newCache[ 2 ] = matcher( elem, context, xml )) ) {
								return true;
							}
						}
					}
				}
			}
		};
}

function elementMatcher( matchers ) {
	return matchers.length > 1 ?
		function( elem, context, xml ) {
			var i = matchers.length;
			while ( i-- ) {
				if ( !matchers[i]( elem, context, xml ) ) {
					return false;
				}
			}
			return true;
		} :
		matchers[0];
}

function multipleContexts( selector, contexts, results ) {
	var i = 0,
		len = contexts.length;
	for ( ; i < len; i++ ) {
		Sizzle( selector, contexts[i], results );
	}
	return results;
}

function condense( unmatched, map, filter, context, xml ) {
	var elem,
		newUnmatched = [],
		i = 0,
		len = unmatched.length,
		mapped = map != null;

	for ( ; i < len; i++ ) {
		if ( (elem = unmatched[i]) ) {
			if ( !filter || filter( elem, context, xml ) ) {
				newUnmatched.push( elem );
				if ( mapped ) {
					map.push( i );
				}
			}
		}
	}

	return newUnmatched;
}

function setMatcher( preFilter, selector, matcher, postFilter, postFinder, postSelector ) {
	if ( postFilter && !postFilter[ expando ] ) {
		postFilter = setMatcher( postFilter );
	}
	if ( postFinder && !postFinder[ expando ] ) {
		postFinder = setMatcher( postFinder, postSelector );
	}
	return markFunction(function( seed, results, context, xml ) {
		var temp, i, elem,
			preMap = [],
			postMap = [],
			preexisting = results.length,

			// Get initial elements from seed or context
			elems = seed || multipleContexts( selector || "*", context.nodeType ? [ context ] : context, [] ),

			// Prefilter to get matcher input, preserving a map for seed-results synchronization
			matcherIn = preFilter && ( seed || !selector ) ?
				condense( elems, preMap, preFilter, context, xml ) :
				elems,

			matcherOut = matcher ?
				// If we have a postFinder, or filtered seed, or non-seed postFilter or preexisting results,
				postFinder || ( seed ? preFilter : preexisting || postFilter ) ?

					// ...intermediate processing is necessary
					[] :

					// ...otherwise use results directly
					results :
				matcherIn;

		// Find primary matches
		if ( matcher ) {
			matcher( matcherIn, matcherOut, context, xml );
		}

		// Apply postFilter
		if ( postFilter ) {
			temp = condense( matcherOut, postMap );
			postFilter( temp, [], context, xml );

			// Un-match failing elements by moving them back to matcherIn
			i = temp.length;
			while ( i-- ) {
				if ( (elem = temp[i]) ) {
					matcherOut[ postMap[i] ] = !(matcherIn[ postMap[i] ] = elem);
				}
			}
		}

		if ( seed ) {
			if ( postFinder || preFilter ) {
				if ( postFinder ) {
					// Get the final matcherOut by condensing this intermediate into postFinder contexts
					temp = [];
					i = matcherOut.length;
					while ( i-- ) {
						if ( (elem = matcherOut[i]) ) {
							// Restore matcherIn since elem is not yet a final match
							temp.push( (matcherIn[i] = elem) );
						}
					}
					postFinder( null, (matcherOut = []), temp, xml );
				}

				// Move matched elements from seed to results to keep them synchronized
				i = matcherOut.length;
				while ( i-- ) {
					if ( (elem = matcherOut[i]) &&
						(temp = postFinder ? indexOf.call( seed, elem ) : preMap[i]) > -1 ) {

						seed[temp] = !(results[temp] = elem);
					}
				}
			}

		// Add elements to results, through postFinder if defined
		} else {
			matcherOut = condense(
				matcherOut === results ?
					matcherOut.splice( preexisting, matcherOut.length ) :
					matcherOut
			);
			if ( postFinder ) {
				postFinder( null, results, matcherOut, xml );
			} else {
				push.apply( results, matcherOut );
			}
		}
	});
}

function matcherFromTokens( tokens ) {
	var checkContext, matcher, j,
		len = tokens.length,
		leadingRelative = Expr.relative[ tokens[0].type ],
		implicitRelative = leadingRelative || Expr.relative[" "],
		i = leadingRelative ? 1 : 0,

		// The foundational matcher ensures that elements are reachable from top-level context(s)
		matchContext = addCombinator( function( elem ) {
			return elem === checkContext;
		}, implicitRelative, true ),
		matchAnyContext = addCombinator( function( elem ) {
			return indexOf.call( checkContext, elem ) > -1;
		}, implicitRelative, true ),
		matchers = [ function( elem, context, xml ) {
			return ( !leadingRelative && ( xml || context !== outermostContext ) ) || (
				(checkContext = context).nodeType ?
					matchContext( elem, context, xml ) :
					matchAnyContext( elem, context, xml ) );
		} ];

	for ( ; i < len; i++ ) {
		if ( (matcher = Expr.relative[ tokens[i].type ]) ) {
			matchers = [ addCombinator(elementMatcher( matchers ), matcher) ];
		} else {
			matcher = Expr.filter[ tokens[i].type ].apply( null, tokens[i].matches );

			// Return special upon seeing a positional matcher
			if ( matcher[ expando ] ) {
				// Find the next relative operator (if any) for proper handling
				j = ++i;
				for ( ; j < len; j++ ) {
					if ( Expr.relative[ tokens[j].type ] ) {
						break;
					}
				}
				return setMatcher(
					i > 1 && elementMatcher( matchers ),
					i > 1 && toSelector(
						// If the preceding token was a descendant combinator, insert an implicit any-element `*`
						tokens.slice( 0, i - 1 ).concat({ value: tokens[ i - 2 ].type === " " ? "*" : "" })
					).replace( rtrim, "$1" ),
					matcher,
					i < j && matcherFromTokens( tokens.slice( i, j ) ),
					j < len && matcherFromTokens( (tokens = tokens.slice( j )) ),
					j < len && toSelector( tokens )
				);
			}
			matchers.push( matcher );
		}
	}

	return elementMatcher( matchers );
}

function matcherFromGroupMatchers( elementMatchers, setMatchers ) {
	var bySet = setMatchers.length > 0,
		byElement = elementMatchers.length > 0,
		superMatcher = function( seed, context, xml, results, outermost ) {
			var elem, j, matcher,
				matchedCount = 0,
				i = "0",
				unmatched = seed && [],
				setMatched = [],
				contextBackup = outermostContext,
				// We must always have either seed elements or outermost context
				elems = seed || byElement && Expr.find["TAG"]( "*", outermost ),
				// Use integer dirruns iff this is the outermost matcher
				dirrunsUnique = (dirruns += contextBackup == null ? 1 : Math.random() || 0.1),
				len = elems.length;

			if ( outermost ) {
				outermostContext = context !== document && context;
			}

			// Add elements passing elementMatchers directly to results
			// Keep `i` a string if there are no elements so `matchedCount` will be "00" below
			// Support: IE<9, Safari
			// Tolerate NodeList properties (IE: "length"; Safari: <number>) matching elements by id
			for ( ; i !== len && (elem = elems[i]) != null; i++ ) {
				if ( byElement && elem ) {
					j = 0;
					while ( (matcher = elementMatchers[j++]) ) {
						if ( matcher( elem, context, xml ) ) {
							results.push( elem );
							break;
						}
					}
					if ( outermost ) {
						dirruns = dirrunsUnique;
					}
				}

				// Track unmatched elements for set filters
				if ( bySet ) {
					// They will have gone through all possible matchers
					if ( (elem = !matcher && elem) ) {
						matchedCount--;
					}

					// Lengthen the array for every element, matched or not
					if ( seed ) {
						unmatched.push( elem );
					}
				}
			}

			// Apply set filters to unmatched elements
			matchedCount += i;
			if ( bySet && i !== matchedCount ) {
				j = 0;
				while ( (matcher = setMatchers[j++]) ) {
					matcher( unmatched, setMatched, context, xml );
				}

				if ( seed ) {
					// Reintegrate element matches to eliminate the need for sorting
					if ( matchedCount > 0 ) {
						while ( i-- ) {
							if ( !(unmatched[i] || setMatched[i]) ) {
								setMatched[i] = pop.call( results );
							}
						}
					}

					// Discard index placeholder values to get only actual matches
					setMatched = condense( setMatched );
				}

				// Add matches to results
				push.apply( results, setMatched );

				// Seedless set matches succeeding multiple successful matchers stipulate sorting
				if ( outermost && !seed && setMatched.length > 0 &&
					( matchedCount + setMatchers.length ) > 1 ) {

					Sizzle.uniqueSort( results );
				}
			}

			// Override manipulation of globals by nested matchers
			if ( outermost ) {
				dirruns = dirrunsUnique;
				outermostContext = contextBackup;
			}

			return unmatched;
		};

	return bySet ?
		markFunction( superMatcher ) :
		superMatcher;
}

compile = Sizzle.compile = function( selector, match /* Internal Use Only */ ) {
	var i,
		setMatchers = [],
		elementMatchers = [],
		cached = compilerCache[ selector + " " ];

	if ( !cached ) {
		// Generate a function of recursive functions that can be used to check each element
		if ( !match ) {
			match = tokenize( selector );
		}
		i = match.length;
		while ( i-- ) {
			cached = matcherFromTokens( match[i] );
			if ( cached[ expando ] ) {
				setMatchers.push( cached );
			} else {
				elementMatchers.push( cached );
			}
		}

		// Cache the compiled function
		cached = compilerCache( selector, matcherFromGroupMatchers( elementMatchers, setMatchers ) );

		// Save selector and tokenization
		cached.selector = selector;
	}
	return cached;
};

/**
 * A low-level selection function that works with Sizzle's compiled
 *  selector functions
 * @param {String|Function} selector A selector or a pre-compiled
 *  selector function built with Sizzle.compile
 * @param {Element} context
 * @param {Array} [results]
 * @param {Array} [seed] A set of elements to match against
 */
select = Sizzle.select = function( selector, context, results, seed ) {
	var i, tokens, token, type, find,
		compiled = typeof selector === "function" && selector,
		match = !seed && tokenize( (selector = compiled.selector || selector) );

	results = results || [];

	// Try to minimize operations if there is no seed and only one group
	if ( match.length === 1 ) {

		// Take a shortcut and set the context if the root selector is an ID
		tokens = match[0] = match[0].slice( 0 );
		if ( tokens.length > 2 && (token = tokens[0]).type === "ID" &&
				support.getById && context.nodeType === 9 && documentIsHTML &&
				Expr.relative[ tokens[1].type ] ) {

			context = ( Expr.find["ID"]( token.matches[0].replace(runescape, funescape), context ) || [] )[0];
			if ( !context ) {
				return results;

			// Precompiled matchers will still verify ancestry, so step up a level
			} else if ( compiled ) {
				context = context.parentNode;
			}

			selector = selector.slice( tokens.shift().value.length );
		}

		// Fetch a seed set for right-to-left matching
		i = matchExpr["needsContext"].test( selector ) ? 0 : tokens.length;
		while ( i-- ) {
			token = tokens[i];

			// Abort if we hit a combinator
			if ( Expr.relative[ (type = token.type) ] ) {
				break;
			}
			if ( (find = Expr.find[ type ]) ) {
				// Search, expanding context for leading sibling combinators
				if ( (seed = find(
					token.matches[0].replace( runescape, funescape ),
					rsibling.test( tokens[0].type ) && testContext( context.parentNode ) || context
				)) ) {

					// If seed is empty or no tokens remain, we can return early
					tokens.splice( i, 1 );
					selector = seed.length && toSelector( tokens );
					if ( !selector ) {
						push.apply( results, seed );
						return results;
					}

					break;
				}
			}
		}
	}

	// Compile and execute a filtering function if one is not provided
	// Provide `match` to avoid retokenization if we modified the selector above
	( compiled || compile( selector, match ) )(
		seed,
		context,
		!documentIsHTML,
		results,
		rsibling.test( selector ) && testContext( context.parentNode ) || context
	);
	return results;
};

// One-time assignments

// Sort stability
support.sortStable = expando.split("").sort( sortOrder ).join("") === expando;

// Support: Chrome<14
// Always assume duplicates if they aren't passed to the comparison function
support.detectDuplicates = !!hasDuplicate;

// Initialize against the default document
setDocument();

// Support: Webkit<537.32 - Safari 6.0.3/Chrome 25 (fixed in Chrome 27)
// Detached nodes confoundingly follow *each other*
support.sortDetached = assert(function( div1 ) {
	// Should return 1, but returns 4 (following)
	return div1.compareDocumentPosition( document.createElement("div") ) & 1;
});

// Support: IE<8
// Prevent attribute/property "interpolation"
// http://msdn.microsoft.com/en-us/library/ms536429%28VS.85%29.aspx
if ( !assert(function( div ) {
	div.innerHTML = "<a href='#'></a>";
	return div.firstChild.getAttribute("href") === "#" ;
}) ) {
	addHandle( "type|href|height|width", function( elem, name, isXML ) {
		if ( !isXML ) {
			return elem.getAttribute( name, name.toLowerCase() === "type" ? 1 : 2 );
		}
	});
}

// Support: IE<9
// Use defaultValue in place of getAttribute("value")
if ( !support.attributes || !assert(function( div ) {
	div.innerHTML = "<input/>";
	div.firstChild.setAttribute( "value", "" );
	return div.firstChild.getAttribute( "value" ) === "";
}) ) {
	addHandle( "value", function( elem, name, isXML ) {
		if ( !isXML && elem.nodeName.toLowerCase() === "input" ) {
			return elem.defaultValue;
		}
	});
}

// Support: IE<9
// Use getAttributeNode to fetch booleans when getAttribute lies
if ( !assert(function( div ) {
	return div.getAttribute("disabled") == null;
}) ) {
	addHandle( booleans, function( elem, name, isXML ) {
		var val;
		if ( !isXML ) {
			return elem[ name ] === true ? name.toLowerCase() :
					(val = elem.getAttributeNode( name )) && val.specified ?
					val.value :
				null;
		}
	});
}

return Sizzle;

})( window );



jQuery.find = Sizzle;
jQuery.expr = Sizzle.selectors;
jQuery.expr[":"] = jQuery.expr.pseudos;
jQuery.unique = Sizzle.uniqueSort;
jQuery.text = Sizzle.getText;
jQuery.isXMLDoc = Sizzle.isXML;
jQuery.contains = Sizzle.contains;



var rneedsContext = jQuery.expr.match.needsContext;

var rsingleTag = (/^<(\w+)\s*\/?>(?:<\/\1>|)$/);



var risSimple = /^.[^:#\[\.,]*$/;

// Implement the identical functionality for filter and not
function winnow( elements, qualifier, not ) {
	if ( jQuery.isFunction( qualifier ) ) {
		return jQuery.grep( elements, function( elem, i ) {
			/* jshint -W018 */
			return !!qualifier.call( elem, i, elem ) !== not;
		});

	}

	if ( qualifier.nodeType ) {
		return jQuery.grep( elements, function( elem ) {
			return ( elem === qualifier ) !== not;
		});

	}

	if ( typeof qualifier === "string" ) {
		if ( risSimple.test( qualifier ) ) {
			return jQuery.filter( qualifier, elements, not );
		}

		qualifier = jQuery.filter( qualifier, elements );
	}

	return jQuery.grep( elements, function( elem ) {
		return ( jQuery.inArray( elem, qualifier ) >= 0 ) !== not;
	});
}

jQuery.filter = function( expr, elems, not ) {
	var elem = elems[ 0 ];

	if ( not ) {
		expr = ":not(" + expr + ")";
	}

	return elems.length === 1 && elem.nodeType === 1 ?
		jQuery.find.matchesSelector( elem, expr ) ? [ elem ] : [] :
		jQuery.find.matches( expr, jQuery.grep( elems, function( elem ) {
			return elem.nodeType === 1;
		}));
};

jQuery.fn.extend({
	find: function( selector ) {
		var i,
			ret = [],
			self = this,
			len = self.length;

		if ( typeof selector !== "string" ) {
			return this.pushStack( jQuery( selector ).filter(function() {
				for ( i = 0; i < len; i++ ) {
					if ( jQuery.contains( self[ i ], this ) ) {
						return true;
					}
				}
			}) );
		}

		for ( i = 0; i < len; i++ ) {
			jQuery.find( selector, self[ i ], ret );
		}

		// Needed because $( selector, context ) becomes $( context ).find( selector )
		ret = this.pushStack( len > 1 ? jQuery.unique( ret ) : ret );
		ret.selector = this.selector ? this.selector + " " + selector : selector;
		return ret;
	},
	filter: function( selector ) {
		return this.pushStack( winnow(this, selector || [], false) );
	},
	not: function( selector ) {
		return this.pushStack( winnow(this, selector || [], true) );
	},
	is: function( selector ) {
		return !!winnow(
			this,

			// If this is a positional/relative selector, check membership in the returned set
			// so $("p:first").is("p:last") won't return true for a doc with two "p".
			typeof selector === "string" && rneedsContext.test( selector ) ?
				jQuery( selector ) :
				selector || [],
			false
		).length;
	}
});


// Initialize a jQuery object


// A central reference to the root jQuery(document)
var rootjQuery,

	// Use the correct document accordingly with window argument (sandbox)
	document = window.document,

	// A simple way to check for HTML strings
	// Prioritize #id over <tag> to avoid XSS via location.hash (#9521)
	// Strict HTML recognition (#11290: must start with <)
	rquickExpr = /^(?:\s*(<[\w\W]+>)[^>]*|#([\w-]*))$/,

	init = jQuery.fn.init = function( selector, context ) {
		var match, elem;

		// HANDLE: $(""), $(null), $(undefined), $(false)
		if ( !selector ) {
			return this;
		}

		// Handle HTML strings
		if ( typeof selector === "string" ) {
			if ( selector.charAt(0) === "<" && selector.charAt( selector.length - 1 ) === ">" && selector.length >= 3 ) {
				// Assume that strings that start and end with <> are HTML and skip the regex check
				match = [ null, selector, null ];

			} else {
				match = rquickExpr.exec( selector );
			}

			// Match html or make sure no context is specified for #id
			if ( match && (match[1] || !context) ) {

				// HANDLE: $(html) -> $(array)
				if ( match[1] ) {
					context = context instanceof jQuery ? context[0] : context;

					// scripts is true for back-compat
					// Intentionally let the error be thrown if parseHTML is not present
					jQuery.merge( this, jQuery.parseHTML(
						match[1],
						context && context.nodeType ? context.ownerDocument || context : document,
						true
					) );

					// HANDLE: $(html, props)
					if ( rsingleTag.test( match[1] ) && jQuery.isPlainObject( context ) ) {
						for ( match in context ) {
							// Properties of context are called as methods if possible
							if ( jQuery.isFunction( this[ match ] ) ) {
								this[ match ]( context[ match ] );

							// ...and otherwise set as attributes
							} else {
								this.attr( match, context[ match ] );
							}
						}
					}

					return this;

				// HANDLE: $(#id)
				} else {
					elem = document.getElementById( match[2] );

					// Check parentNode to catch when Blackberry 4.6 returns
					// nodes that are no longer in the document #6963
					if ( elem && elem.parentNode ) {
						// Handle the case where IE and Opera return items
						// by name instead of ID
						if ( elem.id !== match[2] ) {
							return rootjQuery.find( selector );
						}

						// Otherwise, we inject the element directly into the jQuery object
						this.length = 1;
						this[0] = elem;
					}

					this.context = document;
					this.selector = selector;
					return this;
				}

			// HANDLE: $(expr, $(...))
			} else if ( !context || context.jquery ) {
				return ( context || rootjQuery ).find( selector );

			// HANDLE: $(expr, context)
			// (which is just equivalent to: $(context).find(expr)
			} else {
				return this.constructor( context ).find( selector );
			}

		// HANDLE: $(DOMElement)
		} else if ( selector.nodeType ) {
			this.context = this[0] = selector;
			this.length = 1;
			return this;

		// HANDLE: $(function)
		// Shortcut for document ready
		} else if ( jQuery.isFunction( selector ) ) {
			return typeof rootjQuery.ready !== "undefined" ?
				rootjQuery.ready( selector ) :
				// Execute immediately if ready is not present
				selector( jQuery );
		}

		if ( selector.selector !== undefined ) {
			this.selector = selector.selector;
			this.context = selector.context;
		}

		return jQuery.makeArray( selector, this );
	};

// Give the init function the jQuery prototype for later instantiation
init.prototype = jQuery.fn;

// Initialize central reference
rootjQuery = jQuery( document );


var rparentsprev = /^(?:parents|prev(?:Until|All))/,
	// methods guaranteed to produce a unique set when starting from a unique set
	guaranteedUnique = {
		children: true,
		contents: true,
		next: true,
		prev: true
	};

jQuery.extend({
	dir: function( elem, dir, until ) {
		var matched = [],
			cur = elem[ dir ];

		while ( cur && cur.nodeType !== 9 && (until === undefined || cur.nodeType !== 1 || !jQuery( cur ).is( until )) ) {
			if ( cur.nodeType === 1 ) {
				matched.push( cur );
			}
			cur = cur[dir];
		}
		return matched;
	},

	sibling: function( n, elem ) {
		var r = [];

		for ( ; n; n = n.nextSibling ) {
			if ( n.nodeType === 1 && n !== elem ) {
				r.push( n );
			}
		}

		return r;
	}
});

jQuery.fn.extend({
	has: function( target ) {
		var i,
			targets = jQuery( target, this ),
			len = targets.length;

		return this.filter(function() {
			for ( i = 0; i < len; i++ ) {
				if ( jQuery.contains( this, targets[i] ) ) {
					return true;
				}
			}
		});
	},

	closest: function( selectors, context ) {
		var cur,
			i = 0,
			l = this.length,
			matched = [],
			pos = rneedsContext.test( selectors ) || typeof selectors !== "string" ?
				jQuery( selectors, context || this.context ) :
				0;

		for ( ; i < l; i++ ) {
			for ( cur = this[i]; cur && cur !== context; cur = cur.parentNode ) {
				// Always skip document fragments
				if ( cur.nodeType < 11 && (pos ?
					pos.index(cur) > -1 :

					// Don't pass non-elements to Sizzle
					cur.nodeType === 1 &&
						jQuery.find.matchesSelector(cur, selectors)) ) {

					matched.push( cur );
					break;
				}
			}
		}

		return this.pushStack( matched.length > 1 ? jQuery.unique( matched ) : matched );
	},

	// Determine the position of an element within
	// the matched set of elements
	index: function( elem ) {

		// No argument, return index in parent
		if ( !elem ) {
			return ( this[0] && this[0].parentNode ) ? this.first().prevAll().length : -1;
		}

		// index in selector
		if ( typeof elem === "string" ) {
			return jQuery.inArray( this[0], jQuery( elem ) );
		}

		// Locate the position of the desired element
		return jQuery.inArray(
			// If it receives a jQuery object, the first element is used
			elem.jquery ? elem[0] : elem, this );
	},

	add: function( selector, context ) {
		return this.pushStack(
			jQuery.unique(
				jQuery.merge( this.get(), jQuery( selector, context ) )
			)
		);
	},

	addBack: function( selector ) {
		return this.add( selector == null ?
			this.prevObject : this.prevObject.filter(selector)
		);
	}
});

function sibling( cur, dir ) {
	do {
		cur = cur[ dir ];
	} while ( cur && cur.nodeType !== 1 );

	return cur;
}

jQuery.each({
	parent: function( elem ) {
		var parent = elem.parentNode;
		return parent && parent.nodeType !== 11 ? parent : null;
	},
	parents: function( elem ) {
		return jQuery.dir( elem, "parentNode" );
	},
	parentsUntil: function( elem, i, until ) {
		return jQuery.dir( elem, "parentNode", until );
	},
	next: function( elem ) {
		return sibling( elem, "nextSibling" );
	},
	prev: function( elem ) {
		return sibling( elem, "previousSibling" );
	},
	nextAll: function( elem ) {
		return jQuery.dir( elem, "nextSibling" );
	},
	prevAll: function( elem ) {
		return jQuery.dir( elem, "previousSibling" );
	},
	nextUntil: function( elem, i, until ) {
		return jQuery.dir( elem, "nextSibling", until );
	},
	prevUntil: function( elem, i, until ) {
		return jQuery.dir( elem, "previousSibling", until );
	},
	siblings: function( elem ) {
		return jQuery.sibling( ( elem.parentNode || {} ).firstChild, elem );
	},
	children: function( elem ) {
		return jQuery.sibling( elem.firstChild );
	},
	contents: function( elem ) {
		return jQuery.nodeName( elem, "iframe" ) ?
			elem.contentDocument || elem.contentWindow.document :
			jQuery.merge( [], elem.childNodes );
	}
}, function( name, fn ) {
	jQuery.fn[ name ] = function( until, selector ) {
		var ret = jQuery.map( this, fn, until );

		if ( name.slice( -5 ) !== "Until" ) {
			selector = until;
		}

		if ( selector && typeof selector === "string" ) {
			ret = jQuery.filter( selector, ret );
		}

		if ( this.length > 1 ) {
			// Remove duplicates
			if ( !guaranteedUnique[ name ] ) {
				ret = jQuery.unique( ret );
			}

			// Reverse order for parents* and prev-derivatives
			if ( rparentsprev.test( name ) ) {
				ret = ret.reverse();
			}
		}

		return this.pushStack( ret );
	};
});
var rnotwhite = (/\S+/g);



// String to Object options format cache
var optionsCache = {};

// Convert String-formatted options into Object-formatted ones and store in cache
function createOptions( options ) {
	var object = optionsCache[ options ] = {};
	jQuery.each( options.match( rnotwhite ) || [], function( _, flag ) {
		object[ flag ] = true;
	});
	return object;
}

/*
 * Create a callback list using the following parameters:
 *
 *	options: an optional list of space-separated options that will change how
 *			the callback list behaves or a more traditional option object
 *
 * By default a callback list will act like an event callback list and can be
 * "fired" multiple times.
 *
 * Possible options:
 *
 *	once:			will ensure the callback list can only be fired once (like a Deferred)
 *
 *	memory:			will keep track of previous values and will call any callback added
 *					after the list has been fired right away with the latest "memorized"
 *					values (like a Deferred)
 *
 *	unique:			will ensure a callback can only be added once (no duplicate in the list)
 *
 *	stopOnFalse:	interrupt callings when a callback returns false
 *
 */
jQuery.Callbacks = function( options ) {

	// Convert options from String-formatted to Object-formatted if needed
	// (we check in cache first)
	options = typeof options === "string" ?
		( optionsCache[ options ] || createOptions( options ) ) :
		jQuery.extend( {}, options );

	var // Flag to know if list is currently firing
		firing,
		// Last fire value (for non-forgettable lists)
		memory,
		// Flag to know if list was already fired
		fired,
		// End of the loop when firing
		firingLength,
		// Index of currently firing callback (modified by remove if needed)
		firingIndex,
		// First callback to fire (used internally by add and fireWith)
		firingStart,
		// Actual callback list
		list = [],
		// Stack of fire calls for repeatable lists
		stack = !options.once && [],
		// Fire callbacks
		fire = function( data ) {
			memory = options.memory && data;
			fired = true;
			firingIndex = firingStart || 0;
			firingStart = 0;
			firingLength = list.length;
			firing = true;
			for ( ; list && firingIndex < firingLength; firingIndex++ ) {
				if ( list[ firingIndex ].apply( data[ 0 ], data[ 1 ] ) === false && options.stopOnFalse ) {
					memory = false; // To prevent further calls using add
					break;
				}
			}
			firing = false;
			if ( list ) {
				if ( stack ) {
					if ( stack.length ) {
						fire( stack.shift() );
					}
				} else if ( memory ) {
					list = [];
				} else {
					self.disable();
				}
			}
		},
		// Actual Callbacks object
		self = {
			// Add a callback or a collection of callbacks to the list
			add: function() {
				if ( list ) {
					// First, we save the current length
					var start = list.length;
					(function add( args ) {
						jQuery.each( args, function( _, arg ) {
							var type = jQuery.type( arg );
							if ( type === "function" ) {
								if ( !options.unique || !self.has( arg ) ) {
									list.push( arg );
								}
							} else if ( arg && arg.length && type !== "string" ) {
								// Inspect recursively
								add( arg );
							}
						});
					})( arguments );
					// Do we need to add the callbacks to the
					// current firing batch?
					if ( firing ) {
						firingLength = list.length;
					// With memory, if we're not firing then
					// we should call right away
					} else if ( memory ) {
						firingStart = start;
						fire( memory );
					}
				}
				return this;
			},
			// Remove a callback from the list
			remove: function() {
				if ( list ) {
					jQuery.each( arguments, function( _, arg ) {
						var index;
						while ( ( index = jQuery.inArray( arg, list, index ) ) > -1 ) {
							list.splice( index, 1 );
							// Handle firing indexes
							if ( firing ) {
								if ( index <= firingLength ) {
									firingLength--;
								}
								if ( index <= firingIndex ) {
									firingIndex--;
								}
							}
						}
					});
				}
				return this;
			},
			// Check if a given callback is in the list.
			// If no argument is given, return whether or not list has callbacks attached.
			has: function( fn ) {
				return fn ? jQuery.inArray( fn, list ) > -1 : !!( list && list.length );
			},
			// Remove all callbacks from the list
			empty: function() {
				list = [];
				firingLength = 0;
				return this;
			},
			// Have the list do nothing anymore
			disable: function() {
				list = stack = memory = undefined;
				return this;
			},
			// Is it disabled?
			disabled: function() {
				return !list;
			},
			// Lock the list in its current state
			lock: function() {
				stack = undefined;
				if ( !memory ) {
					self.disable();
				}
				return this;
			},
			// Is it locked?
			locked: function() {
				return !stack;
			},
			// Call all callbacks with the given context and arguments
			fireWith: function( context, args ) {
				if ( list && ( !fired || stack ) ) {
					args = args || [];
					args = [ context, args.slice ? args.slice() : args ];
					if ( firing ) {
						stack.push( args );
					} else {
						fire( args );
					}
				}
				return this;
			},
			// Call all the callbacks with the given arguments
			fire: function() {
				self.fireWith( this, arguments );
				return this;
			},
			// To know if the callbacks have already been called at least once
			fired: function() {
				return !!fired;
			}
		};

	return self;
};


jQuery.extend({

	Deferred: function( func ) {
		var tuples = [
				// action, add listener, listener list, final state
				[ "resolve", "done", jQuery.Callbacks("once memory"), "resolved" ],
				[ "reject", "fail", jQuery.Callbacks("once memory"), "rejected" ],
				[ "notify", "progress", jQuery.Callbacks("memory") ]
			],
			state = "pending",
			promise = {
				state: function() {
					return state;
				},
				always: function() {
					deferred.done( arguments ).fail( arguments );
					return this;
				},
				then: function( /* fnDone, fnFail, fnProgress */ ) {
					var fns = arguments;
					return jQuery.Deferred(function( newDefer ) {
						jQuery.each( tuples, function( i, tuple ) {
							var fn = jQuery.isFunction( fns[ i ] ) && fns[ i ];
							// deferred[ done | fail | progress ] for forwarding actions to newDefer
							deferred[ tuple[1] ](function() {
								var returned = fn && fn.apply( this, arguments );
								if ( returned && jQuery.isFunction( returned.promise ) ) {
									returned.promise()
										.done( newDefer.resolve )
										.fail( newDefer.reject )
										.progress( newDefer.notify );
								} else {
									newDefer[ tuple[ 0 ] + "With" ]( this === promise ? newDefer.promise() : this, fn ? [ returned ] : arguments );
								}
							});
						});
						fns = null;
					}).promise();
				},
				// Get a promise for this deferred
				// If obj is provided, the promise aspect is added to the object
				promise: function( obj ) {
					return obj != null ? jQuery.extend( obj, promise ) : promise;
				}
			},
			deferred = {};

		// Keep pipe for back-compat
		promise.pipe = promise.then;

		// Add list-specific methods
		jQuery.each( tuples, function( i, tuple ) {
			var list = tuple[ 2 ],
				stateString = tuple[ 3 ];

			// promise[ done | fail | progress ] = list.add
			promise[ tuple[1] ] = list.add;

			// Handle state
			if ( stateString ) {
				list.add(function() {
					// state = [ resolved | rejected ]
					state = stateString;

				// [ reject_list | resolve_list ].disable; progress_list.lock
				}, tuples[ i ^ 1 ][ 2 ].disable, tuples[ 2 ][ 2 ].lock );
			}

			// deferred[ resolve | reject | notify ]
			deferred[ tuple[0] ] = function() {
				deferred[ tuple[0] + "With" ]( this === deferred ? promise : this, arguments );
				return this;
			};
			deferred[ tuple[0] + "With" ] = list.fireWith;
		});

		// Make the deferred a promise
		promise.promise( deferred );

		// Call given func if any
		if ( func ) {
			func.call( deferred, deferred );
		}

		// All done!
		return deferred;
	},

	// Deferred helper
	when: function( subordinate /* , ..., subordinateN */ ) {
		var i = 0,
			resolveValues = slice.call( arguments ),
			length = resolveValues.length,

			// the count of uncompleted subordinates
			remaining = length !== 1 || ( subordinate && jQuery.isFunction( subordinate.promise ) ) ? length : 0,

			// the master Deferred. If resolveValues consist of only a single Deferred, just use that.
			deferred = remaining === 1 ? subordinate : jQuery.Deferred(),

			// Update function for both resolve and progress values
			updateFunc = function( i, contexts, values ) {
				return function( value ) {
					contexts[ i ] = this;
					values[ i ] = arguments.length > 1 ? slice.call( arguments ) : value;
					if ( values === progressValues ) {
						deferred.notifyWith( contexts, values );

					} else if ( !(--remaining) ) {
						deferred.resolveWith( contexts, values );
					}
				};
			},

			progressValues, progressContexts, resolveContexts;

		// add listeners to Deferred subordinates; treat others as resolved
		if ( length > 1 ) {
			progressValues = new Array( length );
			progressContexts = new Array( length );
			resolveContexts = new Array( length );
			for ( ; i < length; i++ ) {
				if ( resolveValues[ i ] && jQuery.isFunction( resolveValues[ i ].promise ) ) {
					resolveValues[ i ].promise()
						.done( updateFunc( i, resolveContexts, resolveValues ) )
						.fail( deferred.reject )
						.progress( updateFunc( i, progressContexts, progressValues ) );
				} else {
					--remaining;
				}
			}
		}

		// if we're not waiting on anything, resolve the master
		if ( !remaining ) {
			deferred.resolveWith( resolveContexts, resolveValues );
		}

		return deferred.promise();
	}
});


// The deferred used on DOM ready
var readyList;

jQuery.fn.ready = function( fn ) {
	// Add the callback
	jQuery.ready.promise().done( fn );

	return this;
};

jQuery.extend({
	// Is the DOM ready to be used? Set to true once it occurs.
	isReady: false,

	// A counter to track how many items to wait for before
	// the ready event fires. See #6781
	readyWait: 1,

	// Hold (or release) the ready event
	holdReady: function( hold ) {
		if ( hold ) {
			jQuery.readyWait++;
		} else {
			jQuery.ready( true );
		}
	},

	// Handle when the DOM is ready
	ready: function( wait ) {

		// Abort if there are pending holds or we're already ready
		if ( wait === true ? --jQuery.readyWait : jQuery.isReady ) {
			return;
		}

		// Make sure body exists, at least, in case IE gets a little overzealous (ticket #5443).
		if ( !document.body ) {
			return setTimeout( jQuery.ready );
		}

		// Remember that the DOM is ready
		jQuery.isReady = true;

		// If a normal DOM Ready event fired, decrement, and wait if need be
		if ( wait !== true && --jQuery.readyWait > 0 ) {
			return;
		}

		// If there are functions bound, to execute
		readyList.resolveWith( document, [ jQuery ] );

		// Trigger any bound ready events
		if ( jQuery.fn.triggerHandler ) {
			jQuery( document ).triggerHandler( "ready" );
			jQuery( document ).off( "ready" );
		}
	}
});

/**
 * Clean-up method for dom ready events
 */
function detach() {
	if ( document.addEventListener ) {
		document.removeEventListener( "DOMContentLoaded", completed, false );
		window.removeEventListener( "load", completed, false );

	} else {
		document.detachEvent( "onreadystatechange", completed );
		window.detachEvent( "onload", completed );
	}
}

/**
 * The ready event handler and self cleanup method
 */
function completed() {
	// readyState === "complete" is good enough for us to call the dom ready in oldIE
	if ( document.addEventListener || event.type === "load" || document.readyState === "complete" ) {
		detach();
		jQuery.ready();
	}
}

jQuery.ready.promise = function( obj ) {
	if ( !readyList ) {

		readyList = jQuery.Deferred();

		// Catch cases where $(document).ready() is called after the browser event has already occurred.
		// we once tried to use readyState "interactive" here, but it caused issues like the one
		// discovered by ChrisS here: http://bugs.jquery.com/ticket/12282#comment:15
		if ( document.readyState === "complete" ) {
			// Handle it asynchronously to allow scripts the opportunity to delay ready
			setTimeout( jQuery.ready );

		// Standards-based browsers support DOMContentLoaded
		} else if ( document.addEventListener ) {
			// Use the handy event callback
			document.addEventListener( "DOMContentLoaded", completed, false );

			// A fallback to window.onload, that will always work
			window.addEventListener( "load", completed, false );

		// If IE event model is used
		} else {
			// Ensure firing before onload, maybe late but safe also for iframes
			document.attachEvent( "onreadystatechange", completed );

			// A fallback to window.onload, that will always work
			window.attachEvent( "onload", completed );

			// If IE and not a frame
			// continually check to see if the document is ready
			var top = false;

			try {
				top = window.frameElement == null && document.documentElement;
			} catch(e) {}

			if ( top && top.doScroll ) {
				(function doScrollCheck() {
					if ( !jQuery.isReady ) {

						try {
							// Use the trick by Diego Perini
							// http://javascript.nwbox.com/IEContentLoaded/
							top.doScroll("left");
						} catch(e) {
							return setTimeout( doScrollCheck, 50 );
						}

						// detach all dom ready events
						detach();

						// and execute any waiting functions
						jQuery.ready();
					}
				})();
			}
		}
	}
	return readyList.promise( obj );
};


var strundefined = typeof undefined;



// Support: IE<9
// Iteration over object's inherited properties before its own
var i;
for ( i in jQuery( support ) ) {
	break;
}
support.ownLast = i !== "0";

// Note: most support tests are defined in their respective modules.
// false until the test is run
support.inlineBlockNeedsLayout = false;

// Execute ASAP in case we need to set body.style.zoom
jQuery(function() {
	// Minified: var a,b,c,d
	var val, div, body, container;

	body = document.getElementsByTagName( "body" )[ 0 ];
	if ( !body || !body.style ) {
		// Return for frameset docs that don't have a body
		return;
	}

	// Setup
	div = document.createElement( "div" );
	container = document.createElement( "div" );
	container.style.cssText = "position:absolute;border:0;width:0;height:0;top:0;left:-9999px";
	body.appendChild( container ).appendChild( div );

	if ( typeof div.style.zoom !== strundefined ) {
		// Support: IE<8
		// Check if natively block-level elements act like inline-block
		// elements when setting their display to 'inline' and giving
		// them layout
		div.style.cssText = "display:inline;margin:0;border:0;padding:1px;width:1px;zoom:1";

		support.inlineBlockNeedsLayout = val = div.offsetWidth === 3;
		if ( val ) {
			// Prevent IE 6 from affecting layout for positioned elements #11048
			// Prevent IE from shrinking the body in IE 7 mode #12869
			// Support: IE<8
			body.style.zoom = 1;
		}
	}

	body.removeChild( container );
});




(function() {
	var div = document.createElement( "div" );

	// Execute the test only if not already executed in another module.
	if (support.deleteExpando == null) {
		// Support: IE<9
		support.deleteExpando = true;
		try {
			delete div.test;
		} catch( e ) {
			support.deleteExpando = false;
		}
	}

	// Null elements to avoid leaks in IE.
	div = null;
})();


/**
 * Determines whether an object can have data
 */
jQuery.acceptData = function( elem ) {
	var noData = jQuery.noData[ (elem.nodeName + " ").toLowerCase() ],
		nodeType = +elem.nodeType || 1;

	// Do not set data on non-element DOM nodes because it will not be cleared (#8335).
	return nodeType !== 1 && nodeType !== 9 ?
		false :

		// Nodes accept data unless otherwise specified; rejection can be conditional
		!noData || noData !== true && elem.getAttribute("classid") === noData;
};


var rbrace = /^(?:\{[\w\W]*\}|\[[\w\W]*\])$/,
	rmultiDash = /([A-Z])/g;

function dataAttr( elem, key, data ) {
	// If nothing was found internally, try to fetch any
	// data from the HTML5 data-* attribute
	if ( data === undefined && elem.nodeType === 1 ) {

		var name = "data-" + key.replace( rmultiDash, "-$1" ).toLowerCase();

		data = elem.getAttribute( name );

		if ( typeof data === "string" ) {
			try {
				data = data === "true" ? true :
					data === "false" ? false :
					data === "null" ? null :
					// Only convert to a number if it doesn't change the string
					+data + "" === data ? +data :
					rbrace.test( data ) ? jQuery.parseJSON( data ) :
					data;
			} catch( e ) {}

			// Make sure we set the data so it isn't changed later
			jQuery.data( elem, key, data );

		} else {
			data = undefined;
		}
	}

	return data;
}

// checks a cache object for emptiness
function isEmptyDataObject( obj ) {
	var name;
	for ( name in obj ) {

		// if the public data object is empty, the private is still empty
		if ( name === "data" && jQuery.isEmptyObject( obj[name] ) ) {
			continue;
		}
		if ( name !== "toJSON" ) {
			return false;
		}
	}

	return true;
}

function internalData( elem, name, data, pvt /* Internal Use Only */ ) {
	if ( !jQuery.acceptData( elem ) ) {
		return;
	}

	var ret, thisCache,
		internalKey = jQuery.expando,

		// We have to handle DOM nodes and JS objects differently because IE6-7
		// can't GC object references properly across the DOM-JS boundary
		isNode = elem.nodeType,

		// Only DOM nodes need the global jQuery cache; JS object data is
		// attached directly to the object so GC can occur automatically
		cache = isNode ? jQuery.cache : elem,

		// Only defining an ID for JS objects if its cache already exists allows
		// the code to shortcut on the same path as a DOM node with no cache
		id = isNode ? elem[ internalKey ] : elem[ internalKey ] && internalKey;

	// Avoid doing any more work than we need to when trying to get data on an
	// object that has no data at all
	if ( (!id || !cache[id] || (!pvt && !cache[id].data)) && data === undefined && typeof name === "string" ) {
		return;
	}

	if ( !id ) {
		// Only DOM nodes need a new unique ID for each element since their data
		// ends up in the global cache
		if ( isNode ) {
			id = elem[ internalKey ] = deletedIds.pop() || jQuery.guid++;
		} else {
			id = internalKey;
		}
	}

	if ( !cache[ id ] ) {
		// Avoid exposing jQuery metadata on plain JS objects when the object
		// is serialized using JSON.stringify
		cache[ id ] = isNode ? {} : { toJSON: jQuery.noop };
	}

	// An object can be passed to jQuery.data instead of a key/value pair; this gets
	// shallow copied over onto the existing cache
	if ( typeof name === "object" || typeof name === "function" ) {
		if ( pvt ) {
			cache[ id ] = jQuery.extend( cache[ id ], name );
		} else {
			cache[ id ].data = jQuery.extend( cache[ id ].data, name );
		}
	}

	thisCache = cache[ id ];

	// jQuery data() is stored in a separate object inside the object's internal data
	// cache in order to avoid key collisions between internal data and user-defined
	// data.
	if ( !pvt ) {
		if ( !thisCache.data ) {
			thisCache.data = {};
		}

		thisCache = thisCache.data;
	}

	if ( data !== undefined ) {
		thisCache[ jQuery.camelCase( name ) ] = data;
	}

	// Check for both converted-to-camel and non-converted data property names
	// If a data property was specified
	if ( typeof name === "string" ) {

		// First Try to find as-is property data
		ret = thisCache[ name ];

		// Test for null|undefined property data
		if ( ret == null ) {

			// Try to find the camelCased property
			ret = thisCache[ jQuery.camelCase( name ) ];
		}
	} else {
		ret = thisCache;
	}

	return ret;
}

function internalRemoveData( elem, name, pvt ) {
	if ( !jQuery.acceptData( elem ) ) {
		return;
	}

	var thisCache, i,
		isNode = elem.nodeType,

		// See jQuery.data for more information
		cache = isNode ? jQuery.cache : elem,
		id = isNode ? elem[ jQuery.expando ] : jQuery.expando;

	// If there is already no cache entry for this object, there is no
	// purpose in continuing
	if ( !cache[ id ] ) {
		return;
	}

	if ( name ) {

		thisCache = pvt ? cache[ id ] : cache[ id ].data;

		if ( thisCache ) {

			// Support array or space separated string names for data keys
			if ( !jQuery.isArray( name ) ) {

				// try the string as a key before any manipulation
				if ( name in thisCache ) {
					name = [ name ];
				} else {

					// split the camel cased version by spaces unless a key with the spaces exists
					name = jQuery.camelCase( name );
					if ( name in thisCache ) {
						name = [ name ];
					} else {
						name = name.split(" ");
					}
				}
			} else {
				// If "name" is an array of keys...
				// When data is initially created, via ("key", "val") signature,
				// keys will be converted to camelCase.
				// Since there is no way to tell _how_ a key was added, remove
				// both plain key and camelCase key. #12786
				// This will only penalize the array argument path.
				name = name.concat( jQuery.map( name, jQuery.camelCase ) );
			}

			i = name.length;
			while ( i-- ) {
				delete thisCache[ name[i] ];
			}

			// If there is no data left in the cache, we want to continue
			// and let the cache object itself get destroyed
			if ( pvt ? !isEmptyDataObject(thisCache) : !jQuery.isEmptyObject(thisCache) ) {
				return;
			}
		}
	}

	// See jQuery.data for more information
	if ( !pvt ) {
		delete cache[ id ].data;

		// Don't destroy the parent cache unless the internal data object
		// had been the only thing left in it
		if ( !isEmptyDataObject( cache[ id ] ) ) {
			return;
		}
	}

	// Destroy the cache
	if ( isNode ) {
		jQuery.cleanData( [ elem ], true );

	// Use delete when supported for expandos or `cache` is not a window per isWindow (#10080)
	/* jshint eqeqeq: false */
	} else if ( support.deleteExpando || cache != cache.window ) {
		/* jshint eqeqeq: true */
		delete cache[ id ];

	// When all else fails, null
	} else {
		cache[ id ] = null;
	}
}

jQuery.extend({
	cache: {},

	// The following elements (space-suffixed to avoid Object.prototype collisions)
	// throw uncatchable exceptions if you attempt to set expando properties
	noData: {
		"applet ": true,
		"embed ": true,
		// ...but Flash objects (which have this classid) *can* handle expandos
		"object ": "clsid:D27CDB6E-AE6D-11cf-96B8-444553540000"
	},

	hasData: function( elem ) {
		elem = elem.nodeType ? jQuery.cache[ elem[jQuery.expando] ] : elem[ jQuery.expando ];
		return !!elem && !isEmptyDataObject( elem );
	},

	data: function( elem, name, data ) {
		return internalData( elem, name, data );
	},

	removeData: function( elem, name ) {
		return internalRemoveData( elem, name );
	},

	// For internal use only.
	_data: function( elem, name, data ) {
		return internalData( elem, name, data, true );
	},

	_removeData: function( elem, name ) {
		return internalRemoveData( elem, name, true );
	}
});

jQuery.fn.extend({
	data: function( key, value ) {
		var i, name, data,
			elem = this[0],
			attrs = elem && elem.attributes;

		// Special expections of .data basically thwart jQuery.access,
		// so implement the relevant behavior ourselves

		// Gets all values
		if ( key === undefined ) {
			if ( this.length ) {
				data = jQuery.data( elem );

				if ( elem.nodeType === 1 && !jQuery._data( elem, "parsedAttrs" ) ) {
					i = attrs.length;
					while ( i-- ) {

						// Support: IE11+
						// The attrs elements can be null (#14894)
						if ( attrs[ i ] ) {
							name = attrs[ i ].name;
							if ( name.indexOf( "data-" ) === 0 ) {
								name = jQuery.camelCase( name.slice(5) );
								dataAttr( elem, name, data[ name ] );
							}
						}
					}
					jQuery._data( elem, "parsedAttrs", true );
				}
			}

			return data;
		}

		// Sets multiple values
		if ( typeof key === "object" ) {
			return this.each(function() {
				jQuery.data( this, key );
			});
		}

		return arguments.length > 1 ?

			// Sets one value
			this.each(function() {
				jQuery.data( this, key, value );
			}) :

			// Gets one value
			// Try to fetch any internally stored data first
			elem ? dataAttr( elem, key, jQuery.data( elem, key ) ) : undefined;
	},

	removeData: function( key ) {
		return this.each(function() {
			jQuery.removeData( this, key );
		});
	}
});


jQuery.extend({
	queue: function( elem, type, data ) {
		var queue;

		if ( elem ) {
			type = ( type || "fx" ) + "queue";
			queue = jQuery._data( elem, type );

			// Speed up dequeue by getting out quickly if this is just a lookup
			if ( data ) {
				if ( !queue || jQuery.isArray(data) ) {
					queue = jQuery._data( elem, type, jQuery.makeArray(data) );
				} else {
					queue.push( data );
				}
			}
			return queue || [];
		}
	},

	dequeue: function( elem, type ) {
		type = type || "fx";

		var queue = jQuery.queue( elem, type ),
			startLength = queue.length,
			fn = queue.shift(),
			hooks = jQuery._queueHooks( elem, type ),
			next = function() {
				jQuery.dequeue( elem, type );
			};

		// If the fx queue is dequeued, always remove the progress sentinel
		if ( fn === "inprogress" ) {
			fn = queue.shift();
			startLength--;
		}

		if ( fn ) {

			// Add a progress sentinel to prevent the fx queue from being
			// automatically dequeued
			if ( type === "fx" ) {
				queue.unshift( "inprogress" );
			}

			// clear up the last queue stop function
			delete hooks.stop;
			fn.call( elem, next, hooks );
		}

		if ( !startLength && hooks ) {
			hooks.empty.fire();
		}
	},

	// not intended for public consumption - generates a queueHooks object, or returns the current one
	_queueHooks: function( elem, type ) {
		var key = type + "queueHooks";
		return jQuery._data( elem, key ) || jQuery._data( elem, key, {
			empty: jQuery.Callbacks("once memory").add(function() {
				jQuery._removeData( elem, type + "queue" );
				jQuery._removeData( elem, key );
			})
		});
	}
});

jQuery.fn.extend({
	queue: function( type, data ) {
		var setter = 2;

		if ( typeof type !== "string" ) {
			data = type;
			type = "fx";
			setter--;
		}

		if ( arguments.length < setter ) {
			return jQuery.queue( this[0], type );
		}

		return data === undefined ?
			this :
			this.each(function() {
				var queue = jQuery.queue( this, type, data );

				// ensure a hooks for this queue
				jQuery._queueHooks( this, type );

				if ( type === "fx" && queue[0] !== "inprogress" ) {
					jQuery.dequeue( this, type );
				}
			});
	},
	dequeue: function( type ) {
		return this.each(function() {
			jQuery.dequeue( this, type );
		});
	},
	clearQueue: function( type ) {
		return this.queue( type || "fx", [] );
	},
	// Get a promise resolved when queues of a certain type
	// are emptied (fx is the type by default)
	promise: function( type, obj ) {
		var tmp,
			count = 1,
			defer = jQuery.Deferred(),
			elements = this,
			i = this.length,
			resolve = function() {
				if ( !( --count ) ) {
					defer.resolveWith( elements, [ elements ] );
				}
			};

		if ( typeof type !== "string" ) {
			obj = type;
			type = undefined;
		}
		type = type || "fx";

		while ( i-- ) {
			tmp = jQuery._data( elements[ i ], type + "queueHooks" );
			if ( tmp && tmp.empty ) {
				count++;
				tmp.empty.add( resolve );
			}
		}
		resolve();
		return defer.promise( obj );
	}
});
var pnum = (/[+-]?(?:\d*\.|)\d+(?:[eE][+-]?\d+|)/).source;

var cssExpand = [ "Top", "Right", "Bottom", "Left" ];

var isHidden = function( elem, el ) {
		// isHidden might be called from jQuery#filter function;
		// in that case, element will be second argument
		elem = el || elem;
		return jQuery.css( elem, "display" ) === "none" || !jQuery.contains( elem.ownerDocument, elem );
	};



// Multifunctional method to get and set values of a collection
// The value/s can optionally be executed if it's a function
var access = jQuery.access = function( elems, fn, key, value, chainable, emptyGet, raw ) {
	var i = 0,
		length = elems.length,
		bulk = key == null;

	// Sets many values
	if ( jQuery.type( key ) === "object" ) {
		chainable = true;
		for ( i in key ) {
			jQuery.access( elems, fn, i, key[i], true, emptyGet, raw );
		}

	// Sets one value
	} else if ( value !== undefined ) {
		chainable = true;

		if ( !jQuery.isFunction( value ) ) {
			raw = true;
		}

		if ( bulk ) {
			// Bulk operations run against the entire set
			if ( raw ) {
				fn.call( elems, value );
				fn = null;

			// ...except when executing function values
			} else {
				bulk = fn;
				fn = function( elem, key, value ) {
					return bulk.call( jQuery( elem ), value );
				};
			}
		}

		if ( fn ) {
			for ( ; i < length; i++ ) {
				fn( elems[i], key, raw ? value : value.call( elems[i], i, fn( elems[i], key ) ) );
			}
		}
	}

	return chainable ?
		elems :

		// Gets
		bulk ?
			fn.call( elems ) :
			length ? fn( elems[0], key ) : emptyGet;
};
var rcheckableType = (/^(?:checkbox|radio)$/i);



(function() {
	// Minified: var a,b,c
	var input = document.createElement( "input" ),
		div = document.createElement( "div" ),
		fragment = document.createDocumentFragment();

	// Setup
	div.innerHTML = "  <link/><table></table><a href='/a'>a</a><input type='checkbox'/>";

	// IE strips leading whitespace when .innerHTML is used
	support.leadingWhitespace = div.firstChild.nodeType === 3;

	// Make sure that tbody elements aren't automatically inserted
	// IE will insert them into empty tables
	support.tbody = !div.getElementsByTagName( "tbody" ).length;

	// Make sure that link elements get serialized correctly by innerHTML
	// This requires a wrapper element in IE
	support.htmlSerialize = !!div.getElementsByTagName( "link" ).length;

	// Makes sure cloning an html5 element does not cause problems
	// Where outerHTML is undefined, this still works
	support.html5Clone =
		document.createElement( "nav" ).cloneNode( true ).outerHTML !== "<:nav></:nav>";

	// Check if a disconnected checkbox will retain its checked
	// value of true after appended to the DOM (IE6/7)
	input.type = "checkbox";
	input.checked = true;
	fragment.appendChild( input );
	support.appendChecked = input.checked;

	// Make sure textarea (and checkbox) defaultValue is properly cloned
	// Support: IE6-IE11+
	div.innerHTML = "<textarea>x</textarea>";
	support.noCloneChecked = !!div.cloneNode( true ).lastChild.defaultValue;

	// #11217 - WebKit loses check when the name is after the checked attribute
	fragment.appendChild( div );
	div.innerHTML = "<input type='radio' checked='checked' name='t'/>";

	// Support: Safari 5.1, iOS 5.1, Android 4.x, Android 2.3
	// old WebKit doesn't clone checked state correctly in fragments
	support.checkClone = div.cloneNode( true ).cloneNode( true ).lastChild.checked;

	// Support: IE<9
	// Opera does not clone events (and typeof div.attachEvent === undefined).
	// IE9-10 clones events bound via attachEvent, but they don't trigger with .click()
	support.noCloneEvent = true;
	if ( div.attachEvent ) {
		div.attachEvent( "onclick", function() {
			support.noCloneEvent = false;
		});

		div.cloneNode( true ).click();
	}

	// Execute the test only if not already executed in another module.
	if (support.deleteExpando == null) {
		// Support: IE<9
		support.deleteExpando = true;
		try {
			delete div.test;
		} catch( e ) {
			support.deleteExpando = false;
		}
	}
})();


(function() {
	var i, eventName,
		div = document.createElement( "div" );

	// Support: IE<9 (lack submit/change bubble), Firefox 23+ (lack focusin event)
	for ( i in { submit: true, change: true, focusin: true }) {
		eventName = "on" + i;

		if ( !(support[ i + "Bubbles" ] = eventName in window) ) {
			// Beware of CSP restrictions (https://developer.mozilla.org/en/Security/CSP)
			div.setAttribute( eventName, "t" );
			support[ i + "Bubbles" ] = div.attributes[ eventName ].expando === false;
		}
	}

	// Null elements to avoid leaks in IE.
	div = null;
})();


var rformElems = /^(?:input|select|textarea)$/i,
	rkeyEvent = /^key/,
	rmouseEvent = /^(?:mouse|pointer|contextmenu)|click/,
	rfocusMorph = /^(?:focusinfocus|focusoutblur)$/,
	rtypenamespace = /^([^.]*)(?:\.(.+)|)$/;

function returnTrue() {
	return true;
}

function returnFalse() {
	return false;
}

function safeActiveElement() {
	try {
		return document.activeElement;
	} catch ( err ) { }
}

/*
 * Helper functions for managing events -- not part of the public interface.
 * Props to Dean Edwards' addEvent library for many of the ideas.
 */
jQuery.event = {

	global: {},

	add: function( elem, types, handler, data, selector ) {
		var tmp, events, t, handleObjIn,
			special, eventHandle, handleObj,
			handlers, type, namespaces, origType,
			elemData = jQuery._data( elem );

		// Don't attach events to noData or text/comment nodes (but allow plain objects)
		if ( !elemData ) {
			return;
		}

		// Caller can pass in an object of custom data in lieu of the handler
		if ( handler.handler ) {
			handleObjIn = handler;
			handler = handleObjIn.handler;
			selector = handleObjIn.selector;
		}

		// Make sure that the handler has a unique ID, used to find/remove it later
		if ( !handler.guid ) {
			handler.guid = jQuery.guid++;
		}

		// Init the element's event structure and main handler, if this is the first
		if ( !(events = elemData.events) ) {
			events = elemData.events = {};
		}
		if ( !(eventHandle = elemData.handle) ) {
			eventHandle = elemData.handle = function( e ) {
				// Discard the second event of a jQuery.event.trigger() and
				// when an event is called after a page has unloaded
				return typeof jQuery !== strundefined && (!e || jQuery.event.triggered !== e.type) ?
					jQuery.event.dispatch.apply( eventHandle.elem, arguments ) :
					undefined;
			};
			// Add elem as a property of the handle fn to prevent a memory leak with IE non-native events
			eventHandle.elem = elem;
		}

		// Handle multiple events separated by a space
		types = ( types || "" ).match( rnotwhite ) || [ "" ];
		t = types.length;
		while ( t-- ) {
			tmp = rtypenamespace.exec( types[t] ) || [];
			type = origType = tmp[1];
			namespaces = ( tmp[2] || "" ).split( "." ).sort();

			// There *must* be a type, no attaching namespace-only handlers
			if ( !type ) {
				continue;
			}

			// If event changes its type, use the special event handlers for the changed type
			special = jQuery.event.special[ type ] || {};

			// If selector defined, determine special event api type, otherwise given type
			type = ( selector ? special.delegateType : special.bindType ) || type;

			// Update special based on newly reset type
			special = jQuery.event.special[ type ] || {};

			// handleObj is passed to all event handlers
			handleObj = jQuery.extend({
				type: type,
				origType: origType,
				data: data,
				handler: handler,
				guid: handler.guid,
				selector: selector,
				needsContext: selector && jQuery.expr.match.needsContext.test( selector ),
				namespace: namespaces.join(".")
			}, handleObjIn );

			// Init the event handler queue if we're the first
			if ( !(handlers = events[ type ]) ) {
				handlers = events[ type ] = [];
				handlers.delegateCount = 0;

				// Only use addEventListener/attachEvent if the special events handler returns false
				if ( !special.setup || special.setup.call( elem, data, namespaces, eventHandle ) === false ) {
					// Bind the global event handler to the element
					if ( elem.addEventListener ) {
						elem.addEventListener( type, eventHandle, false );

					} else if ( elem.attachEvent ) {
						elem.attachEvent( "on" + type, eventHandle );
					}
				}
			}

			if ( special.add ) {
				special.add.call( elem, handleObj );

				if ( !handleObj.handler.guid ) {
					handleObj.handler.guid = handler.guid;
				}
			}

			// Add to the element's handler list, delegates in front
			if ( selector ) {
				handlers.splice( handlers.delegateCount++, 0, handleObj );
			} else {
				handlers.push( handleObj );
			}

			// Keep track of which events have ever been used, for event optimization
			jQuery.event.global[ type ] = true;
		}

		// Nullify elem to prevent memory leaks in IE
		elem = null;
	},

	// Detach an event or set of events from an element
	remove: function( elem, types, handler, selector, mappedTypes ) {
		var j, handleObj, tmp,
			origCount, t, events,
			special, handlers, type,
			namespaces, origType,
			elemData = jQuery.hasData( elem ) && jQuery._data( elem );

		if ( !elemData || !(events = elemData.events) ) {
			return;
		}

		// Once for each type.namespace in types; type may be omitted
		types = ( types || "" ).match( rnotwhite ) || [ "" ];
		t = types.length;
		while ( t-- ) {
			tmp = rtypenamespace.exec( types[t] ) || [];
			type = origType = tmp[1];
			namespaces = ( tmp[2] || "" ).split( "." ).sort();

			// Unbind all events (on this namespace, if provided) for the element
			if ( !type ) {
				for ( type in events ) {
					jQuery.event.remove( elem, type + types[ t ], handler, selector, true );
				}
				continue;
			}

			special = jQuery.event.special[ type ] || {};
			type = ( selector ? special.delegateType : special.bindType ) || type;
			handlers = events[ type ] || [];
			tmp = tmp[2] && new RegExp( "(^|\\.)" + namespaces.join("\\.(?:.*\\.|)") + "(\\.|$)" );

			// Remove matching events
			origCount = j = handlers.length;
			while ( j-- ) {
				handleObj = handlers[ j ];

				if ( ( mappedTypes || origType === handleObj.origType ) &&
					( !handler || handler.guid === handleObj.guid ) &&
					( !tmp || tmp.test( handleObj.namespace ) ) &&
					( !selector || selector === handleObj.selector || selector === "**" && handleObj.selector ) ) {
					handlers.splice( j, 1 );

					if ( handleObj.selector ) {
						handlers.delegateCount--;
					}
					if ( special.remove ) {
						special.remove.call( elem, handleObj );
					}
				}
			}

			// Remove generic event handler if we removed something and no more handlers exist
			// (avoids potential for endless recursion during removal of special event handlers)
			if ( origCount && !handlers.length ) {
				if ( !special.teardown || special.teardown.call( elem, namespaces, elemData.handle ) === false ) {
					jQuery.removeEvent( elem, type, elemData.handle );
				}

				delete events[ type ];
			}
		}

		// Remove the expando if it's no longer used
		if ( jQuery.isEmptyObject( events ) ) {
			delete elemData.handle;

			// removeData also checks for emptiness and clears the expando if empty
			// so use it instead of delete
			jQuery._removeData( elem, "events" );
		}
	},

	trigger: function( event, data, elem, onlyHandlers ) {
		var handle, ontype, cur,
			bubbleType, special, tmp, i,
			eventPath = [ elem || document ],
			type = hasOwn.call( event, "type" ) ? event.type : event,
			namespaces = hasOwn.call( event, "namespace" ) ? event.namespace.split(".") : [];

		cur = tmp = elem = elem || document;

		// Don't do events on text and comment nodes
		if ( elem.nodeType === 3 || elem.nodeType === 8 ) {
			return;
		}

		// focus/blur morphs to focusin/out; ensure we're not firing them right now
		if ( rfocusMorph.test( type + jQuery.event.triggered ) ) {
			return;
		}

		if ( type.indexOf(".") >= 0 ) {
			// Namespaced trigger; create a regexp to match event type in handle()
			namespaces = type.split(".");
			type = namespaces.shift();
			namespaces.sort();
		}
		ontype = type.indexOf(":") < 0 && "on" + type;

		// Caller can pass in a jQuery.Event object, Object, or just an event type string
		event = event[ jQuery.expando ] ?
			event :
			new jQuery.Event( type, typeof event === "object" && event );

		// Trigger bitmask: & 1 for native handlers; & 2 for jQuery (always true)
		event.isTrigger = onlyHandlers ? 2 : 3;
		event.namespace = namespaces.join(".");
		event.namespace_re = event.namespace ?
			new RegExp( "(^|\\.)" + namespaces.join("\\.(?:.*\\.|)") + "(\\.|$)" ) :
			null;

		// Clean up the event in case it is being reused
		event.result = undefined;
		if ( !event.target ) {
			event.target = elem;
		}

		// Clone any incoming data and prepend the event, creating the handler arg list
		data = data == null ?
			[ event ] :
			jQuery.makeArray( data, [ event ] );

		// Allow special events to draw outside the lines
		special = jQuery.event.special[ type ] || {};
		if ( !onlyHandlers && special.trigger && special.trigger.apply( elem, data ) === false ) {
			return;
		}

		// Determine event propagation path in advance, per W3C events spec (#9951)
		// Bubble up to document, then to window; watch for a global ownerDocument var (#9724)
		if ( !onlyHandlers && !special.noBubble && !jQuery.isWindow( elem ) ) {

			bubbleType = special.delegateType || type;
			if ( !rfocusMorph.test( bubbleType + type ) ) {
				cur = cur.parentNode;
			}
			for ( ; cur; cur = cur.parentNode ) {
				eventPath.push( cur );
				tmp = cur;
			}

			// Only add window if we got to document (e.g., not plain obj or detached DOM)
			if ( tmp === (elem.ownerDocument || document) ) {
				eventPath.push( tmp.defaultView || tmp.parentWindow || window );
			}
		}

		// Fire handlers on the event path
		i = 0;
		while ( (cur = eventPath[i++]) && !event.isPropagationStopped() ) {

			event.type = i > 1 ?
				bubbleType :
				special.bindType || type;

			// jQuery handler
			handle = ( jQuery._data( cur, "events" ) || {} )[ event.type ] && jQuery._data( cur, "handle" );
			if ( handle ) {
				handle.apply( cur, data );
			}

			// Native handler
			handle = ontype && cur[ ontype ];
			if ( handle && handle.apply && jQuery.acceptData( cur ) ) {
				event.result = handle.apply( cur, data );
				if ( event.result === false ) {
					event.preventDefault();
				}
			}
		}
		event.type = type;

		// If nobody prevented the default action, do it now
		if ( !onlyHandlers && !event.isDefaultPrevented() ) {

			if ( (!special._default || special._default.apply( eventPath.pop(), data ) === false) &&
				jQuery.acceptData( elem ) ) {

				// Call a native DOM method on the target with the same name name as the event.
				// Can't use an .isFunction() check here because IE6/7 fails that test.
				// Don't do default actions on window, that's where global variables be (#6170)
				if ( ontype && elem[ type ] && !jQuery.isWindow( elem ) ) {

					// Don't re-trigger an onFOO event when we call its FOO() method
					tmp = elem[ ontype ];

					if ( tmp ) {
						elem[ ontype ] = null;
					}

					// Prevent re-triggering of the same event, since we already bubbled it above
					jQuery.event.triggered = type;
					try {
						elem[ type ]();
					} catch ( e ) {
						// IE<9 dies on focus/blur to hidden element (#1486,#12518)
						// only reproducible on winXP IE8 native, not IE9 in IE8 mode
					}
					jQuery.event.triggered = undefined;

					if ( tmp ) {
						elem[ ontype ] = tmp;
					}
				}
			}
		}

		return event.result;
	},

	dispatch: function( event ) {

		// Make a writable jQuery.Event from the native event object
		event = jQuery.event.fix( event );

		var i, ret, handleObj, matched, j,
			handlerQueue = [],
			args = slice.call( arguments ),
			handlers = ( jQuery._data( this, "events" ) || {} )[ event.type ] || [],
			special = jQuery.event.special[ event.type ] || {};

		// Use the fix-ed jQuery.Event rather than the (read-only) native event
		args[0] = event;
		event.delegateTarget = this;

		// Call the preDispatch hook for the mapped type, and let it bail if desired
		if ( special.preDispatch && special.preDispatch.call( this, event ) === false ) {
			return;
		}

		// Determine handlers
		handlerQueue = jQuery.event.handlers.call( this, event, handlers );

		// Run delegates first; they may want to stop propagation beneath us
		i = 0;
		while ( (matched = handlerQueue[ i++ ]) && !event.isPropagationStopped() ) {
			event.currentTarget = matched.elem;

			j = 0;
			while ( (handleObj = matched.handlers[ j++ ]) && !event.isImmediatePropagationStopped() ) {

				// Triggered event must either 1) have no namespace, or
				// 2) have namespace(s) a subset or equal to those in the bound event (both can have no namespace).
				if ( !event.namespace_re || event.namespace_re.test( handleObj.namespace ) ) {

					event.handleObj = handleObj;
					event.data = handleObj.data;

					ret = ( (jQuery.event.special[ handleObj.origType ] || {}).handle || handleObj.handler )
							.apply( matched.elem, args );

					if ( ret !== undefined ) {
						if ( (event.result = ret) === false ) {
							event.preventDefault();
							event.stopPropagation();
						}
					}
				}
			}
		}

		// Call the postDispatch hook for the mapped type
		if ( special.postDispatch ) {
			special.postDispatch.call( this, event );
		}

		return event.result;
	},

	handlers: function( event, handlers ) {
		var sel, handleObj, matches, i,
			handlerQueue = [],
			delegateCount = handlers.delegateCount,
			cur = event.target;

		// Find delegate handlers
		// Black-hole SVG <use> instance trees (#13180)
		// Avoid non-left-click bubbling in Firefox (#3861)
		if ( delegateCount && cur.nodeType && (!event.button || event.type !== "click") ) {

			/* jshint eqeqeq: false */
			for ( ; cur != this; cur = cur.parentNode || this ) {
				/* jshint eqeqeq: true */

				// Don't check non-elements (#13208)
				// Don't process clicks on disabled elements (#6911, #8165, #11382, #11764)
				if ( cur.nodeType === 1 && (cur.disabled !== true || event.type !== "click") ) {
					matches = [];
					for ( i = 0; i < delegateCount; i++ ) {
						handleObj = handlers[ i ];

						// Don't conflict with Object.prototype properties (#13203)
						sel = handleObj.selector + " ";

						if ( matches[ sel ] === undefined ) {
							matches[ sel ] = handleObj.needsContext ?
								jQuery( sel, this ).index( cur ) >= 0 :
								jQuery.find( sel, this, null, [ cur ] ).length;
						}
						if ( matches[ sel ] ) {
							matches.push( handleObj );
						}
					}
					if ( matches.length ) {
						handlerQueue.push({ elem: cur, handlers: matches });
					}
				}
			}
		}

		// Add the remaining (directly-bound) handlers
		if ( delegateCount < handlers.length ) {
			handlerQueue.push({ elem: this, handlers: handlers.slice( delegateCount ) });
		}

		return handlerQueue;
	},

	fix: function( event ) {
		if ( event[ jQuery.expando ] ) {
			return event;
		}

		// Create a writable copy of the event object and normalize some properties
		var i, prop, copy,
			type = event.type,
			originalEvent = event,
			fixHook = this.fixHooks[ type ];

		if ( !fixHook ) {
			this.fixHooks[ type ] = fixHook =
				rmouseEvent.test( type ) ? this.mouseHooks :
				rkeyEvent.test( type ) ? this.keyHooks :
				{};
		}
		copy = fixHook.props ? this.props.concat( fixHook.props ) : this.props;

		event = new jQuery.Event( originalEvent );

		i = copy.length;
		while ( i-- ) {
			prop = copy[ i ];
			event[ prop ] = originalEvent[ prop ];
		}

		// Support: IE<9
		// Fix target property (#1925)
		if ( !event.target ) {
			event.target = originalEvent.srcElement || document;
		}

		// Support: Chrome 23+, Safari?
		// Target should not be a text node (#504, #13143)
		if ( event.target.nodeType === 3 ) {
			event.target = event.target.parentNode;
		}

		// Support: IE<9
		// For mouse/key events, metaKey==false if it's undefined (#3368, #11328)
		event.metaKey = !!event.metaKey;

		return fixHook.filter ? fixHook.filter( event, originalEvent ) : event;
	},

	// Includes some event props shared by KeyEvent and MouseEvent
	props: "altKey bubbles cancelable ctrlKey currentTarget eventPhase metaKey relatedTarget shiftKey target timeStamp view which".split(" "),

	fixHooks: {},

	keyHooks: {
		props: "char charCode key keyCode".split(" "),
		filter: function( event, original ) {

			// Add which for key events
			if ( event.which == null ) {
				event.which = original.charCode != null ? original.charCode : original.keyCode;
			}

			return event;
		}
	},

	mouseHooks: {
		props: "button buttons clientX clientY fromElement offsetX offsetY pageX pageY screenX screenY toElement".split(" "),
		filter: function( event, original ) {
			var body, eventDoc, doc,
				button = original.button,
				fromElement = original.fromElement;

			// Calculate pageX/Y if missing and clientX/Y available
			if ( event.pageX == null && original.clientX != null ) {
				eventDoc = event.target.ownerDocument || document;
				doc = eventDoc.documentElement;
				body = eventDoc.body;

				event.pageX = original.clientX + ( doc && doc.scrollLeft || body && body.scrollLeft || 0 ) - ( doc && doc.clientLeft || body && body.clientLeft || 0 );
				event.pageY = original.clientY + ( doc && doc.scrollTop  || body && body.scrollTop  || 0 ) - ( doc && doc.clientTop  || body && body.clientTop  || 0 );
			}

			// Add relatedTarget, if necessary
			if ( !event.relatedTarget && fromElement ) {
				event.relatedTarget = fromElement === event.target ? original.toElement : fromElement;
			}

			// Add which for click: 1 === left; 2 === middle; 3 === right
			// Note: button is not normalized, so don't use it
			if ( !event.which && button !== undefined ) {
				event.which = ( button & 1 ? 1 : ( button & 2 ? 3 : ( button & 4 ? 2 : 0 ) ) );
			}

			return event;
		}
	},

	special: {
		load: {
			// Prevent triggered image.load events from bubbling to window.load
			noBubble: true
		},
		focus: {
			// Fire native event if possible so blur/focus sequence is correct
			trigger: function() {
				if ( this !== safeActiveElement() && this.focus ) {
					try {
						this.focus();
						return false;
					} catch ( e ) {
						// Support: IE<9
						// If we error on focus to hidden element (#1486, #12518),
						// let .trigger() run the handlers
					}
				}
			},
			delegateType: "focusin"
		},
		blur: {
			trigger: function() {
				if ( this === safeActiveElement() && this.blur ) {
					this.blur();
					return false;
				}
			},
			delegateType: "focusout"
		},
		click: {
			// For checkbox, fire native event so checked state will be right
			trigger: function() {
				if ( jQuery.nodeName( this, "input" ) && this.type === "checkbox" && this.click ) {
					this.click();
					return false;
				}
			},

			// For cross-browser consistency, don't fire native .click() on links
			_default: function( event ) {
				return jQuery.nodeName( event.target, "a" );
			}
		},

		beforeunload: {
			postDispatch: function( event ) {

				// Support: Firefox 20+
				// Firefox doesn't alert if the returnValue field is not set.
				if ( event.result !== undefined && event.originalEvent ) {
					event.originalEvent.returnValue = event.result;
				}
			}
		}
	},

	simulate: function( type, elem, event, bubble ) {
		// Piggyback on a donor event to simulate a different one.
		// Fake originalEvent to avoid donor's stopPropagation, but if the
		// simulated event prevents default then we do the same on the donor.
		var e = jQuery.extend(
			new jQuery.Event(),
			event,
			{
				type: type,
				isSimulated: true,
				originalEvent: {}
			}
		);
		if ( bubble ) {
			jQuery.event.trigger( e, null, elem );
		} else {
			jQuery.event.dispatch.call( elem, e );
		}
		if ( e.isDefaultPrevented() ) {
			event.preventDefault();
		}
	}
};

jQuery.removeEvent = document.removeEventListener ?
	function( elem, type, handle ) {
		if ( elem.removeEventListener ) {
			elem.removeEventListener( type, handle, false );
		}
	} :
	function( elem, type, handle ) {
		var name = "on" + type;

		if ( elem.detachEvent ) {

			// #8545, #7054, preventing memory leaks for custom events in IE6-8
			// detachEvent needed property on element, by name of that event, to properly expose it to GC
			if ( typeof elem[ name ] === strundefined ) {
				elem[ name ] = null;
			}

			elem.detachEvent( name, handle );
		}
	};

jQuery.Event = function( src, props ) {
	// Allow instantiation without the 'new' keyword
	if ( !(this instanceof jQuery.Event) ) {
		return new jQuery.Event( src, props );
	}

	// Event object
	if ( src && src.type ) {
		this.originalEvent = src;
		this.type = src.type;

		// Events bubbling up the document may have been marked as prevented
		// by a handler lower down the tree; reflect the correct value.
		this.isDefaultPrevented = src.defaultPrevented ||
				src.defaultPrevented === undefined &&
				// Support: IE < 9, Android < 4.0
				src.returnValue === false ?
			returnTrue :
			returnFalse;

	// Event type
	} else {
		this.type = src;
	}

	// Put explicitly provided properties onto the event object
	if ( props ) {
		jQuery.extend( this, props );
	}

	// Create a timestamp if incoming event doesn't have one
	this.timeStamp = src && src.timeStamp || jQuery.now();

	// Mark it as fixed
	this[ jQuery.expando ] = true;
};

// jQuery.Event is based on DOM3 Events as specified by the ECMAScript Language Binding
// http://www.w3.org/TR/2003/WD-DOM-Level-3-Events-20030331/ecma-script-binding.html
jQuery.Event.prototype = {
	isDefaultPrevented: returnFalse,
	isPropagationStopped: returnFalse,
	isImmediatePropagationStopped: returnFalse,

	preventDefault: function() {
		var e = this.originalEvent;

		this.isDefaultPrevented = returnTrue;
		if ( !e ) {
			return;
		}

		// If preventDefault exists, run it on the original event
		if ( e.preventDefault ) {
			e.preventDefault();

		// Support: IE
		// Otherwise set the returnValue property of the original event to false
		} else {
			e.returnValue = false;
		}
	},
	stopPropagation: function() {
		var e = this.originalEvent;

		this.isPropagationStopped = returnTrue;
		if ( !e ) {
			return;
		}
		// If stopPropagation exists, run it on the original event
		if ( e.stopPropagation ) {
			e.stopPropagation();
		}

		// Support: IE
		// Set the cancelBubble property of the original event to true
		e.cancelBubble = true;
	},
	stopImmediatePropagation: function() {
		var e = this.originalEvent;

		this.isImmediatePropagationStopped = returnTrue;

		if ( e && e.stopImmediatePropagation ) {
			e.stopImmediatePropagation();
		}

		this.stopPropagation();
	}
};

// Create mouseenter/leave events using mouseover/out and event-time checks
jQuery.each({
	mouseenter: "mouseover",
	mouseleave: "mouseout",
	pointerenter: "pointerover",
	pointerleave: "pointerout"
}, function( orig, fix ) {
	jQuery.event.special[ orig ] = {
		delegateType: fix,
		bindType: fix,

		handle: function( event ) {
			var ret,
				target = this,
				related = event.relatedTarget,
				handleObj = event.handleObj;

			// For mousenter/leave call the handler if related is outside the target.
			// NB: No relatedTarget if the mouse left/entered the browser window
			if ( !related || (related !== target && !jQuery.contains( target, related )) ) {
				event.type = handleObj.origType;
				ret = handleObj.handler.apply( this, arguments );
				event.type = fix;
			}
			return ret;
		}
	};
});

// IE submit delegation
if ( !support.submitBubbles ) {

	jQuery.event.special.submit = {
		setup: function() {
			// Only need this for delegated form submit events
			if ( jQuery.nodeName( this, "form" ) ) {
				return false;
			}

			// Lazy-add a submit handler when a descendant form may potentially be submitted
			jQuery.event.add( this, "click._submit keypress._submit", function( e ) {
				// Node name check avoids a VML-related crash in IE (#9807)
				var elem = e.target,
					form = jQuery.nodeName( elem, "input" ) || jQuery.nodeName( elem, "button" ) ? elem.form : undefined;
				if ( form && !jQuery._data( form, "submitBubbles" ) ) {
					jQuery.event.add( form, "submit._submit", function( event ) {
						event._submit_bubble = true;
					});
					jQuery._data( form, "submitBubbles", true );
				}
			});
			// return undefined since we don't need an event listener
		},

		postDispatch: function( event ) {
			// If form was submitted by the user, bubble the event up the tree
			if ( event._submit_bubble ) {
				delete event._submit_bubble;
				if ( this.parentNode && !event.isTrigger ) {
					jQuery.event.simulate( "submit", this.parentNode, event, true );
				}
			}
		},

		teardown: function() {
			// Only need this for delegated form submit events
			if ( jQuery.nodeName( this, "form" ) ) {
				return false;
			}

			// Remove delegated handlers; cleanData eventually reaps submit handlers attached above
			jQuery.event.remove( this, "._submit" );
		}
	};
}

// IE change delegation and checkbox/radio fix
if ( !support.changeBubbles ) {

	jQuery.event.special.change = {

		setup: function() {

			if ( rformElems.test( this.nodeName ) ) {
				// IE doesn't fire change on a check/radio until blur; trigger it on click
				// after a propertychange. Eat the blur-change in special.change.handle.
				// This still fires onchange a second time for check/radio after blur.
				if ( this.type === "checkbox" || this.type === "radio" ) {
					jQuery.event.add( this, "propertychange._change", function( event ) {
						if ( event.originalEvent.propertyName === "checked" ) {
							this._just_changed = true;
						}
					});
					jQuery.event.add( this, "click._change", function( event ) {
						if ( this._just_changed && !event.isTrigger ) {
							this._just_changed = false;
						}
						// Allow triggered, simulated change events (#11500)
						jQuery.event.simulate( "change", this, event, true );
					});
				}
				return false;
			}
			// Delegated event; lazy-add a change handler on descendant inputs
			jQuery.event.add( this, "beforeactivate._change", function( e ) {
				var elem = e.target;

				if ( rformElems.test( elem.nodeName ) && !jQuery._data( elem, "changeBubbles" ) ) {
					jQuery.event.add( elem, "change._change", function( event ) {
						if ( this.parentNode && !event.isSimulated && !event.isTrigger ) {
							jQuery.event.simulate( "change", this.parentNode, event, true );
						}
					});
					jQuery._data( elem, "changeBubbles", true );
				}
			});
		},

		handle: function( event ) {
			var elem = event.target;

			// Swallow native change events from checkbox/radio, we already triggered them above
			if ( this !== elem || event.isSimulated || event.isTrigger || (elem.type !== "radio" && elem.type !== "checkbox") ) {
				return event.handleObj.handler.apply( this, arguments );
			}
		},

		teardown: function() {
			jQuery.event.remove( this, "._change" );

			return !rformElems.test( this.nodeName );
		}
	};
}

// Create "bubbling" focus and blur events
if ( !support.focusinBubbles ) {
	jQuery.each({ focus: "focusin", blur: "focusout" }, function( orig, fix ) {

		// Attach a single capturing handler on the document while someone wants focusin/focusout
		var handler = function( event ) {
				jQuery.event.simulate( fix, event.target, jQuery.event.fix( event ), true );
			};

		jQuery.event.special[ fix ] = {
			setup: function() {
				var doc = this.ownerDocument || this,
					attaches = jQuery._data( doc, fix );

				if ( !attaches ) {
					doc.addEventListener( orig, handler, true );
				}
				jQuery._data( doc, fix, ( attaches || 0 ) + 1 );
			},
			teardown: function() {
				var doc = this.ownerDocument || this,
					attaches = jQuery._data( doc, fix ) - 1;

				if ( !attaches ) {
					doc.removeEventListener( orig, handler, true );
					jQuery._removeData( doc, fix );
				} else {
					jQuery._data( doc, fix, attaches );
				}
			}
		};
	});
}

jQuery.fn.extend({

	on: function( types, selector, data, fn, /*INTERNAL*/ one ) {
		var type, origFn;

		// Types can be a map of types/handlers
		if ( typeof types === "object" ) {
			// ( types-Object, selector, data )
			if ( typeof selector !== "string" ) {
				// ( types-Object, data )
				data = data || selector;
				selector = undefined;
			}
			for ( type in types ) {
				this.on( type, selector, data, types[ type ], one );
			}
			return this;
		}

		if ( data == null && fn == null ) {
			// ( types, fn )
			fn = selector;
			data = selector = undefined;
		} else if ( fn == null ) {
			if ( typeof selector === "string" ) {
				// ( types, selector, fn )
				fn = data;
				data = undefined;
			} else {
				// ( types, data, fn )
				fn = data;
				data = selector;
				selector = undefined;
			}
		}
		if ( fn === false ) {
			fn = returnFalse;
		} else if ( !fn ) {
			return this;
		}

		if ( one === 1 ) {
			origFn = fn;
			fn = function( event ) {
				// Can use an empty set, since event contains the info
				jQuery().off( event );
				return origFn.apply( this, arguments );
			};
			// Use same guid so caller can remove using origFn
			fn.guid = origFn.guid || ( origFn.guid = jQuery.guid++ );
		}
		return this.each( function() {
			jQuery.event.add( this, types, fn, data, selector );
		});
	},
	one: function( types, selector, data, fn ) {
		return this.on( types, selector, data, fn, 1 );
	},
	off: function( types, selector, fn ) {
		var handleObj, type;
		if ( types && types.preventDefault && types.handleObj ) {
			// ( event )  dispatched jQuery.Event
			handleObj = types.handleObj;
			jQuery( types.delegateTarget ).off(
				handleObj.namespace ? handleObj.origType + "." + handleObj.namespace : handleObj.origType,
				handleObj.selector,
				handleObj.handler
			);
			return this;
		}
		if ( typeof types === "object" ) {
			// ( types-object [, selector] )
			for ( type in types ) {
				this.off( type, selector, types[ type ] );
			}
			return this;
		}
		if ( selector === false || typeof selector === "function" ) {
			// ( types [, fn] )
			fn = selector;
			selector = undefined;
		}
		if ( fn === false ) {
			fn = returnFalse;
		}
		return this.each(function() {
			jQuery.event.remove( this, types, fn, selector );
		});
	},

	trigger: function( type, data ) {
		return this.each(function() {
			jQuery.event.trigger( type, data, this );
		});
	},
	triggerHandler: function( type, data ) {
		var elem = this[0];
		if ( elem ) {
			return jQuery.event.trigger( type, data, elem, true );
		}
	}
});


function createSafeFragment( document ) {
	var list = nodeNames.split( "|" ),
		safeFrag = document.createDocumentFragment();

	if ( safeFrag.createElement ) {
		while ( list.length ) {
			safeFrag.createElement(
				list.pop()
			);
		}
	}
	return safeFrag;
}

var nodeNames = "abbr|article|aside|audio|bdi|canvas|data|datalist|details|figcaption|figure|footer|" +
		"header|hgroup|mark|meter|nav|output|progress|section|summary|time|video",
	rinlinejQuery = / jQuery\d+="(?:null|\d+)"/g,
	rnoshimcache = new RegExp("<(?:" + nodeNames + ")[\\s/>]", "i"),
	rleadingWhitespace = /^\s+/,
	rxhtmlTag = /<(?!area|br|col|embed|hr|img|input|link|meta|param)(([\w:]+)[^>]*)\/>/gi,
	rtagName = /<([\w:]+)/,
	rtbody = /<tbody/i,
	rhtml = /<|&#?\w+;/,
	rnoInnerhtml = /<(?:script|style|link)/i,
	// checked="checked" or checked
	rchecked = /checked\s*(?:[^=]|=\s*.checked.)/i,
	rscriptType = /^$|\/(?:java|ecma)script/i,
	rscriptTypeMasked = /^true\/(.*)/,
	rcleanScript = /^\s*<!(?:\[CDATA\[|--)|(?:\]\]|--)>\s*$/g,

	// We have to close these tags to support XHTML (#13200)
	wrapMap = {
		option: [ 1, "<select multiple='multiple'>", "</select>" ],
		legend: [ 1, "<fieldset>", "</fieldset>" ],
		area: [ 1, "<map>", "</map>" ],
		param: [ 1, "<object>", "</object>" ],
		thead: [ 1, "<table>", "</table>" ],
		tr: [ 2, "<table><tbody>", "</tbody></table>" ],
		col: [ 2, "<table><tbody></tbody><colgroup>", "</colgroup></table>" ],
		td: [ 3, "<table><tbody><tr>", "</tr></tbody></table>" ],

		// IE6-8 can't serialize link, script, style, or any html5 (NoScope) tags,
		// unless wrapped in a div with non-breaking characters in front of it.
		_default: support.htmlSerialize ? [ 0, "", "" ] : [ 1, "X<div>", "</div>"  ]
	},
	safeFragment = createSafeFragment( document ),
	fragmentDiv = safeFragment.appendChild( document.createElement("div") );

wrapMap.optgroup = wrapMap.option;
wrapMap.tbody = wrapMap.tfoot = wrapMap.colgroup = wrapMap.caption = wrapMap.thead;
wrapMap.th = wrapMap.td;

function getAll( context, tag ) {
	var elems, elem,
		i = 0,
		found = typeof context.getElementsByTagName !== strundefined ? context.getElementsByTagName( tag || "*" ) :
			typeof context.querySelectorAll !== strundefined ? context.querySelectorAll( tag || "*" ) :
			undefined;

	if ( !found ) {
		for ( found = [], elems = context.childNodes || context; (elem = elems[i]) != null; i++ ) {
			if ( !tag || jQuery.nodeName( elem, tag ) ) {
				found.push( elem );
			} else {
				jQuery.merge( found, getAll( elem, tag ) );
			}
		}
	}

	return tag === undefined || tag && jQuery.nodeName( context, tag ) ?
		jQuery.merge( [ context ], found ) :
		found;
}

// Used in buildFragment, fixes the defaultChecked property
function fixDefaultChecked( elem ) {
	if ( rcheckableType.test( elem.type ) ) {
		elem.defaultChecked = elem.checked;
	}
}

// Support: IE<8
// Manipulating tables requires a tbody
function manipulationTarget( elem, content ) {
	return jQuery.nodeName( elem, "table" ) &&
		jQuery.nodeName( content.nodeType !== 11 ? content : content.firstChild, "tr" ) ?

		elem.getElementsByTagName("tbody")[0] ||
			elem.appendChild( elem.ownerDocument.createElement("tbody") ) :
		elem;
}

// Replace/restore the type attribute of script elements for safe DOM manipulation
function disableScript( elem ) {
	elem.type = (jQuery.find.attr( elem, "type" ) !== null) + "/" + elem.type;
	return elem;
}
function restoreScript( elem ) {
	var match = rscriptTypeMasked.exec( elem.type );
	if ( match ) {
		elem.type = match[1];
	} else {
		elem.removeAttribute("type");
	}
	return elem;
}

// Mark scripts as having already been evaluated
function setGlobalEval( elems, refElements ) {
	var elem,
		i = 0;
	for ( ; (elem = elems[i]) != null; i++ ) {
		jQuery._data( elem, "globalEval", !refElements || jQuery._data( refElements[i], "globalEval" ) );
	}
}

function cloneCopyEvent( src, dest ) {

	if ( dest.nodeType !== 1 || !jQuery.hasData( src ) ) {
		return;
	}

	var type, i, l,
		oldData = jQuery._data( src ),
		curData = jQuery._data( dest, oldData ),
		events = oldData.events;

	if ( events ) {
		delete curData.handle;
		curData.events = {};

		for ( type in events ) {
			for ( i = 0, l = events[ type ].length; i < l; i++ ) {
				jQuery.event.add( dest, type, events[ type ][ i ] );
			}
		}
	}

	// make the cloned public data object a copy from the original
	if ( curData.data ) {
		curData.data = jQuery.extend( {}, curData.data );
	}
}

function fixCloneNodeIssues( src, dest ) {
	var nodeName, e, data;

	// We do not need to do anything for non-Elements
	if ( dest.nodeType !== 1 ) {
		return;
	}

	nodeName = dest.nodeName.toLowerCase();

	// IE6-8 copies events bound via attachEvent when using cloneNode.
	if ( !support.noCloneEvent && dest[ jQuery.expando ] ) {
		data = jQuery._data( dest );

		for ( e in data.events ) {
			jQuery.removeEvent( dest, e, data.handle );
		}

		// Event data gets referenced instead of copied if the expando gets copied too
		dest.removeAttribute( jQuery.expando );
	}

	// IE blanks contents when cloning scripts, and tries to evaluate newly-set text
	if ( nodeName === "script" && dest.text !== src.text ) {
		disableScript( dest ).text = src.text;
		restoreScript( dest );

	// IE6-10 improperly clones children of object elements using classid.
	// IE10 throws NoModificationAllowedError if parent is null, #12132.
	} else if ( nodeName === "object" ) {
		if ( dest.parentNode ) {
			dest.outerHTML = src.outerHTML;
		}

		// This path appears unavoidable for IE9. When cloning an object
		// element in IE9, the outerHTML strategy above is not sufficient.
		// If the src has innerHTML and the destination does not,
		// copy the src.innerHTML into the dest.innerHTML. #10324
		if ( support.html5Clone && ( src.innerHTML && !jQuery.trim(dest.innerHTML) ) ) {
			dest.innerHTML = src.innerHTML;
		}

	} else if ( nodeName === "input" && rcheckableType.test( src.type ) ) {
		// IE6-8 fails to persist the checked state of a cloned checkbox
		// or radio button. Worse, IE6-7 fail to give the cloned element
		// a checked appearance if the defaultChecked value isn't also set

		dest.defaultChecked = dest.checked = src.checked;

		// IE6-7 get confused and end up setting the value of a cloned
		// checkbox/radio button to an empty string instead of "on"
		if ( dest.value !== src.value ) {
			dest.value = src.value;
		}

	// IE6-8 fails to return the selected option to the default selected
	// state when cloning options
	} else if ( nodeName === "option" ) {
		dest.defaultSelected = dest.selected = src.defaultSelected;

	// IE6-8 fails to set the defaultValue to the correct value when
	// cloning other types of input fields
	} else if ( nodeName === "input" || nodeName === "textarea" ) {
		dest.defaultValue = src.defaultValue;
	}
}

jQuery.extend({
	clone: function( elem, dataAndEvents, deepDataAndEvents ) {
		var destElements, node, clone, i, srcElements,
			inPage = jQuery.contains( elem.ownerDocument, elem );

		if ( support.html5Clone || jQuery.isXMLDoc(elem) || !rnoshimcache.test( "<" + elem.nodeName + ">" ) ) {
			clone = elem.cloneNode( true );

		// IE<=8 does not properly clone detached, unknown element nodes
		} else {
			fragmentDiv.innerHTML = elem.outerHTML;
			fragmentDiv.removeChild( clone = fragmentDiv.firstChild );
		}

		if ( (!support.noCloneEvent || !support.noCloneChecked) &&
				(elem.nodeType === 1 || elem.nodeType === 11) && !jQuery.isXMLDoc(elem) ) {

			// We eschew Sizzle here for performance reasons: http://jsperf.com/getall-vs-sizzle/2
			destElements = getAll( clone );
			srcElements = getAll( elem );

			// Fix all IE cloning issues
			for ( i = 0; (node = srcElements[i]) != null; ++i ) {
				// Ensure that the destination node is not null; Fixes #9587
				if ( destElements[i] ) {
					fixCloneNodeIssues( node, destElements[i] );
				}
			}
		}

		// Copy the events from the original to the clone
		if ( dataAndEvents ) {
			if ( deepDataAndEvents ) {
				srcElements = srcElements || getAll( elem );
				destElements = destElements || getAll( clone );

				for ( i = 0; (node = srcElements[i]) != null; i++ ) {
					cloneCopyEvent( node, destElements[i] );
				}
			} else {
				cloneCopyEvent( elem, clone );
			}
		}

		// Preserve script evaluation history
		destElements = getAll( clone, "script" );
		if ( destElements.length > 0 ) {
			setGlobalEval( destElements, !inPage && getAll( elem, "script" ) );
		}

		destElements = srcElements = node = null;

		// Return the cloned set
		return clone;
	},

	buildFragment: function( elems, context, scripts, selection ) {
		var j, elem, contains,
			tmp, tag, tbody, wrap,
			l = elems.length,

			// Ensure a safe fragment
			safe = createSafeFragment( context ),

			nodes = [],
			i = 0;

		for ( ; i < l; i++ ) {
			elem = elems[ i ];

			if ( elem || elem === 0 ) {

				// Add nodes directly
				if ( jQuery.type( elem ) === "object" ) {
					jQuery.merge( nodes, elem.nodeType ? [ elem ] : elem );

				// Convert non-html into a text node
				} else if ( !rhtml.test( elem ) ) {
					nodes.push( context.createTextNode( elem ) );

				// Convert html into DOM nodes
				} else {
					tmp = tmp || safe.appendChild( context.createElement("div") );

					// Deserialize a standard representation
					tag = (rtagName.exec( elem ) || [ "", "" ])[ 1 ].toLowerCase();
					wrap = wrapMap[ tag ] || wrapMap._default;

					tmp.innerHTML = wrap[1] + elem.replace( rxhtmlTag, "<$1></$2>" ) + wrap[2];

					// Descend through wrappers to the right content
					j = wrap[0];
					while ( j-- ) {
						tmp = tmp.lastChild;
					}

					// Manually add leading whitespace removed by IE
					if ( !support.leadingWhitespace && rleadingWhitespace.test( elem ) ) {
						nodes.push( context.createTextNode( rleadingWhitespace.exec( elem )[0] ) );
					}

					// Remove IE's autoinserted <tbody> from table fragments
					if ( !support.tbody ) {

						// String was a <table>, *may* have spurious <tbody>
						elem = tag === "table" && !rtbody.test( elem ) ?
							tmp.firstChild :

							// String was a bare <thead> or <tfoot>
							wrap[1] === "<table>" && !rtbody.test( elem ) ?
								tmp :
								0;

						j = elem && elem.childNodes.length;
						while ( j-- ) {
							if ( jQuery.nodeName( (tbody = elem.childNodes[j]), "tbody" ) && !tbody.childNodes.length ) {
								elem.removeChild( tbody );
							}
						}
					}

					jQuery.merge( nodes, tmp.childNodes );

					// Fix #12392 for WebKit and IE > 9
					tmp.textContent = "";

					// Fix #12392 for oldIE
					while ( tmp.firstChild ) {
						tmp.removeChild( tmp.firstChild );
					}

					// Remember the top-level container for proper cleanup
					tmp = safe.lastChild;
				}
			}
		}

		// Fix #11356: Clear elements from fragment
		if ( tmp ) {
			safe.removeChild( tmp );
		}

		// Reset defaultChecked for any radios and checkboxes
		// about to be appended to the DOM in IE 6/7 (#8060)
		if ( !support.appendChecked ) {
			jQuery.grep( getAll( nodes, "input" ), fixDefaultChecked );
		}

		i = 0;
		while ( (elem = nodes[ i++ ]) ) {

			// #4087 - If origin and destination elements are the same, and this is
			// that element, do not do anything
			if ( selection && jQuery.inArray( elem, selection ) !== -1 ) {
				continue;
			}

			contains = jQuery.contains( elem.ownerDocument, elem );

			// Append to fragment
			tmp = getAll( safe.appendChild( elem ), "script" );

			// Preserve script evaluation history
			if ( contains ) {
				setGlobalEval( tmp );
			}

			// Capture executables
			if ( scripts ) {
				j = 0;
				while ( (elem = tmp[ j++ ]) ) {
					if ( rscriptType.test( elem.type || "" ) ) {
						scripts.push( elem );
					}
				}
			}
		}

		tmp = null;

		return safe;
	},

	cleanData: function( elems, /* internal */ acceptData ) {
		var elem, type, id, data,
			i = 0,
			internalKey = jQuery.expando,
			cache = jQuery.cache,
			deleteExpando = support.deleteExpando,
			special = jQuery.event.special;

		for ( ; (elem = elems[i]) != null; i++ ) {
			if ( acceptData || jQuery.acceptData( elem ) ) {

				id = elem[ internalKey ];
				data = id && cache[ id ];

				if ( data ) {
					if ( data.events ) {
						for ( type in data.events ) {
							if ( special[ type ] ) {
								jQuery.event.remove( elem, type );

							// This is a shortcut to avoid jQuery.event.remove's overhead
							} else {
								jQuery.removeEvent( elem, type, data.handle );
							}
						}
					}

					// Remove cache only if it was not already removed by jQuery.event.remove
					if ( cache[ id ] ) {

						delete cache[ id ];

						// IE does not allow us to delete expando properties from nodes,
						// nor does it have a removeAttribute function on Document nodes;
						// we must handle all of these cases
						if ( deleteExpando ) {
							delete elem[ internalKey ];

						} else if ( typeof elem.removeAttribute !== strundefined ) {
							elem.removeAttribute( internalKey );

						} else {
							elem[ internalKey ] = null;
						}

						deletedIds.push( id );
					}
				}
			}
		}
	}
});

jQuery.fn.extend({
	text: function( value ) {
		return access( this, function( value ) {
			return value === undefined ?
				jQuery.text( this ) :
				this.empty().append( ( this[0] && this[0].ownerDocument || document ).createTextNode( value ) );
		}, null, value, arguments.length );
	},

	append: function() {
		return this.domManip( arguments, function( elem ) {
			if ( this.nodeType === 1 || this.nodeType === 11 || this.nodeType === 9 ) {
				var target = manipulationTarget( this, elem );
				target.appendChild( elem );
			}
		});
	},

	prepend: function() {
		return this.domManip( arguments, function( elem ) {
			if ( this.nodeType === 1 || this.nodeType === 11 || this.nodeType === 9 ) {
				var target = manipulationTarget( this, elem );
				target.insertBefore( elem, target.firstChild );
			}
		});
	},

	before: function() {
		return this.domManip( arguments, function( elem ) {
			if ( this.parentNode ) {
				this.parentNode.insertBefore( elem, this );
			}
		});
	},

	after: function() {
		return this.domManip( arguments, function( elem ) {
			if ( this.parentNode ) {
				this.parentNode.insertBefore( elem, this.nextSibling );
			}
		});
	},

	remove: function( selector, keepData /* Internal Use Only */ ) {
		var elem,
			elems = selector ? jQuery.filter( selector, this ) : this,
			i = 0;

		for ( ; (elem = elems[i]) != null; i++ ) {

			if ( !keepData && elem.nodeType === 1 ) {
				jQuery.cleanData( getAll( elem ) );
			}

			if ( elem.parentNode ) {
				if ( keepData && jQuery.contains( elem.ownerDocument, elem ) ) {
					setGlobalEval( getAll( elem, "script" ) );
				}
				elem.parentNode.removeChild( elem );
			}
		}

		return this;
	},

	empty: function() {
		var elem,
			i = 0;

		for ( ; (elem = this[i]) != null; i++ ) {
			// Remove element nodes and prevent memory leaks
			if ( elem.nodeType === 1 ) {
				jQuery.cleanData( getAll( elem, false ) );
			}

			// Remove any remaining nodes
			while ( elem.firstChild ) {
				elem.removeChild( elem.firstChild );
			}

			// If this is a select, ensure that it displays empty (#12336)
			// Support: IE<9
			if ( elem.options && jQuery.nodeName( elem, "select" ) ) {
				elem.options.length = 0;
			}
		}

		return this;
	},

	clone: function( dataAndEvents, deepDataAndEvents ) {
		dataAndEvents = dataAndEvents == null ? false : dataAndEvents;
		deepDataAndEvents = deepDataAndEvents == null ? dataAndEvents : deepDataAndEvents;

		return this.map(function() {
			return jQuery.clone( this, dataAndEvents, deepDataAndEvents );
		});
	},

	html: function( value ) {
		return access( this, function( value ) {
			var elem = this[ 0 ] || {},
				i = 0,
				l = this.length;

			if ( value === undefined ) {
				return elem.nodeType === 1 ?
					elem.innerHTML.replace( rinlinejQuery, "" ) :
					undefined;
			}

			// See if we can take a shortcut and just use innerHTML
			if ( typeof value === "string" && !rnoInnerhtml.test( value ) &&
				( support.htmlSerialize || !rnoshimcache.test( value )  ) &&
				( support.leadingWhitespace || !rleadingWhitespace.test( value ) ) &&
				!wrapMap[ (rtagName.exec( value ) || [ "", "" ])[ 1 ].toLowerCase() ] ) {

				value = value.replace( rxhtmlTag, "<$1></$2>" );

				try {
					for (; i < l; i++ ) {
						// Remove element nodes and prevent memory leaks
						elem = this[i] || {};
						if ( elem.nodeType === 1 ) {
							jQuery.cleanData( getAll( elem, false ) );
							elem.innerHTML = value;
						}
					}

					elem = 0;

				// If using innerHTML throws an exception, use the fallback method
				} catch(e) {}
			}

			if ( elem ) {
				this.empty().append( value );
			}
		}, null, value, arguments.length );
	},

	replaceWith: function() {
		var arg = arguments[ 0 ];

		// Make the changes, replacing each context element with the new content
		this.domManip( arguments, function( elem ) {
			arg = this.parentNode;

			jQuery.cleanData( getAll( this ) );

			if ( arg ) {
				arg.replaceChild( elem, this );
			}
		});

		// Force removal if there was no new content (e.g., from empty arguments)
		return arg && (arg.length || arg.nodeType) ? this : this.remove();
	},

	detach: function( selector ) {
		return this.remove( selector, true );
	},

	domManip: function( args, callback ) {

		// Flatten any nested arrays
		args = concat.apply( [], args );

		var first, node, hasScripts,
			scripts, doc, fragment,
			i = 0,
			l = this.length,
			set = this,
			iNoClone = l - 1,
			value = args[0],
			isFunction = jQuery.isFunction( value );

		// We can't cloneNode fragments that contain checked, in WebKit
		if ( isFunction ||
				( l > 1 && typeof value === "string" &&
					!support.checkClone && rchecked.test( value ) ) ) {
			return this.each(function( index ) {
				var self = set.eq( index );
				if ( isFunction ) {
					args[0] = value.call( this, index, self.html() );
				}
				self.domManip( args, callback );
			});
		}

		if ( l ) {
			fragment = jQuery.buildFragment( args, this[ 0 ].ownerDocument, false, this );
			first = fragment.firstChild;

			if ( fragment.childNodes.length === 1 ) {
				fragment = first;
			}

			if ( first ) {
				scripts = jQuery.map( getAll( fragment, "script" ), disableScript );
				hasScripts = scripts.length;

				// Use the original fragment for the last item instead of the first because it can end up
				// being emptied incorrectly in certain situations (#8070).
				for ( ; i < l; i++ ) {
					node = fragment;

					if ( i !== iNoClone ) {
						node = jQuery.clone( node, true, true );

						// Keep references to cloned scripts for later restoration
						if ( hasScripts ) {
							jQuery.merge( scripts, getAll( node, "script" ) );
						}
					}

					callback.call( this[i], node, i );
				}

				if ( hasScripts ) {
					doc = scripts[ scripts.length - 1 ].ownerDocument;

					// Reenable scripts
					jQuery.map( scripts, restoreScript );

					// Evaluate executable scripts on first document insertion
					for ( i = 0; i < hasScripts; i++ ) {
						node = scripts[ i ];
						if ( rscriptType.test( node.type || "" ) &&
							!jQuery._data( node, "globalEval" ) && jQuery.contains( doc, node ) ) {

							if ( node.src ) {
								// Optional AJAX dependency, but won't run scripts if not present
								if ( jQuery._evalUrl ) {
									jQuery._evalUrl( node.src );
								}
							} else {
								jQuery.globalEval( ( node.text || node.textContent || node.innerHTML || "" ).replace( rcleanScript, "" ) );
							}
						}
					}
				}

				// Fix #11809: Avoid leaking memory
				fragment = first = null;
			}
		}

		return this;
	}
});

jQuery.each({
	appendTo: "append",
	prependTo: "prepend",
	insertBefore: "before",
	insertAfter: "after",
	replaceAll: "replaceWith"
}, function( name, original ) {
	jQuery.fn[ name ] = function( selector ) {
		var elems,
			i = 0,
			ret = [],
			insert = jQuery( selector ),
			last = insert.length - 1;

		for ( ; i <= last; i++ ) {
			elems = i === last ? this : this.clone(true);
			jQuery( insert[i] )[ original ]( elems );

			// Modern browsers can apply jQuery collections as arrays, but oldIE needs a .get()
			push.apply( ret, elems.get() );
		}

		return this.pushStack( ret );
	};
});


var iframe,
	elemdisplay = {};

/**
 * Retrieve the actual display of a element
 * @param {String} name nodeName of the element
 * @param {Object} doc Document object
 */
// Called only from within defaultDisplay
function actualDisplay( name, doc ) {
	var style,
		elem = jQuery( doc.createElement( name ) ).appendTo( doc.body ),

		// getDefaultComputedStyle might be reliably used only on attached element
		display = window.getDefaultComputedStyle && ( style = window.getDefaultComputedStyle( elem[ 0 ] ) ) ?

			// Use of this method is a temporary fix (more like optmization) until something better comes along,
			// since it was removed from specification and supported only in FF
			style.display : jQuery.css( elem[ 0 ], "display" );

	// We don't have any data stored on the element,
	// so use "detach" method as fast way to get rid of the element
	elem.detach();

	return display;
}

/**
 * Try to determine the default display value of an element
 * @param {String} nodeName
 */
function defaultDisplay( nodeName ) {
	var doc = document,
		display = elemdisplay[ nodeName ];

	if ( !display ) {
		display = actualDisplay( nodeName, doc );

		// If the simple way fails, read from inside an iframe
		if ( display === "none" || !display ) {

			// Use the already-created iframe if possible
			iframe = (iframe || jQuery( "<iframe frameborder='0' width='0' height='0'/>" )).appendTo( doc.documentElement );

			// Always write a new HTML skeleton so Webkit and Firefox don't choke on reuse
			doc = ( iframe[ 0 ].contentWindow || iframe[ 0 ].contentDocument ).document;

			// Support: IE
			doc.write();
			doc.close();

			display = actualDisplay( nodeName, doc );
			iframe.detach();
		}

		// Store the correct default display
		elemdisplay[ nodeName ] = display;
	}

	return display;
}


(function() {
	var shrinkWrapBlocksVal;

	support.shrinkWrapBlocks = function() {
		if ( shrinkWrapBlocksVal != null ) {
			return shrinkWrapBlocksVal;
		}

		// Will be changed later if needed.
		shrinkWrapBlocksVal = false;

		// Minified: var b,c,d
		var div, body, container;

		body = document.getElementsByTagName( "body" )[ 0 ];
		if ( !body || !body.style ) {
			// Test fired too early or in an unsupported environment, exit.
			return;
		}

		// Setup
		div = document.createElement( "div" );
		container = document.createElement( "div" );
		container.style.cssText = "position:absolute;border:0;width:0;height:0;top:0;left:-9999px";
		body.appendChild( container ).appendChild( div );

		// Support: IE6
		// Check if elements with layout shrink-wrap their children
		if ( typeof div.style.zoom !== strundefined ) {
			// Reset CSS: box-sizing; display; margin; border
			div.style.cssText =
				// Support: Firefox<29, Android 2.3
				// Vendor-prefix box-sizing
				"-webkit-box-sizing:content-box;-moz-box-sizing:content-box;" +
				"box-sizing:content-box;display:block;margin:0;border:0;" +
				"padding:1px;width:1px;zoom:1";
			div.appendChild( document.createElement( "div" ) ).style.width = "5px";
			shrinkWrapBlocksVal = div.offsetWidth !== 3;
		}

		body.removeChild( container );

		return shrinkWrapBlocksVal;
	};

})();
var rmargin = (/^margin/);

var rnumnonpx = new RegExp( "^(" + pnum + ")(?!px)[a-z%]+$", "i" );



var getStyles, curCSS,
	rposition = /^(top|right|bottom|left)$/;

if ( window.getComputedStyle ) {
	getStyles = function( elem ) {
		return elem.ownerDocument.defaultView.getComputedStyle( elem, null );
	};

	curCSS = function( elem, name, computed ) {
		var width, minWidth, maxWidth, ret,
			style = elem.style;

		computed = computed || getStyles( elem );

		// getPropertyValue is only needed for .css('filter') in IE9, see #12537
		ret = computed ? computed.getPropertyValue( name ) || computed[ name ] : undefined;

		if ( computed ) {

			if ( ret === "" && !jQuery.contains( elem.ownerDocument, elem ) ) {
				ret = jQuery.style( elem, name );
			}

			// A tribute to the "awesome hack by Dean Edwards"
			// Chrome < 17 and Safari 5.0 uses "computed value" instead of "used value" for margin-right
			// Safari 5.1.7 (at least) returns percentage for a larger set of values, but width seems to be reliably pixels
			// this is against the CSSOM draft spec: http://dev.w3.org/csswg/cssom/#resolved-values
			if ( rnumnonpx.test( ret ) && rmargin.test( name ) ) {

				// Remember the original values
				width = style.width;
				minWidth = style.minWidth;
				maxWidth = style.maxWidth;

				// Put in the new values to get a computed value out
				style.minWidth = style.maxWidth = style.width = ret;
				ret = computed.width;

				// Revert the changed values
				style.width = width;
				style.minWidth = minWidth;
				style.maxWidth = maxWidth;
			}
		}

		// Support: IE
		// IE returns zIndex value as an integer.
		return ret === undefined ?
			ret :
			ret + "";
	};
} else if ( document.documentElement.currentStyle ) {
	getStyles = function( elem ) {
		return elem.currentStyle;
	};

	curCSS = function( elem, name, computed ) {
		var left, rs, rsLeft, ret,
			style = elem.style;

		computed = computed || getStyles( elem );
		ret = computed ? computed[ name ] : undefined;

		// Avoid setting ret to empty string here
		// so we don't default to auto
		if ( ret == null && style && style[ name ] ) {
			ret = style[ name ];
		}

		// From the awesome hack by Dean Edwards
		// http://erik.eae.net/archives/2007/07/27/18.54.15/#comment-102291

		// If we're not dealing with a regular pixel number
		// but a number that has a weird ending, we need to convert it to pixels
		// but not position css attributes, as those are proportional to the parent element instead
		// and we can't measure the parent instead because it might trigger a "stacking dolls" problem
		if ( rnumnonpx.test( ret ) && !rposition.test( name ) ) {

			// Remember the original values
			left = style.left;
			rs = elem.runtimeStyle;
			rsLeft = rs && rs.left;

			// Put in the new values to get a computed value out
			if ( rsLeft ) {
				rs.left = elem.currentStyle.left;
			}
			style.left = name === "fontSize" ? "1em" : ret;
			ret = style.pixelLeft + "px";

			// Revert the changed values
			style.left = left;
			if ( rsLeft ) {
				rs.left = rsLeft;
			}
		}

		// Support: IE
		// IE returns zIndex value as an integer.
		return ret === undefined ?
			ret :
			ret + "" || "auto";
	};
}




function addGetHookIf( conditionFn, hookFn ) {
	// Define the hook, we'll check on the first run if it's really needed.
	return {
		get: function() {
			var condition = conditionFn();

			if ( condition == null ) {
				// The test was not ready at this point; screw the hook this time
				// but check again when needed next time.
				return;
			}

			if ( condition ) {
				// Hook not needed (or it's not possible to use it due to missing dependency),
				// remove it.
				// Since there are no other hooks for marginRight, remove the whole object.
				delete this.get;
				return;
			}

			// Hook needed; redefine it so that the support test is not executed again.

			return (this.get = hookFn).apply( this, arguments );
		}
	};
}


(function() {
	// Minified: var b,c,d,e,f,g, h,i
	var div, style, a, pixelPositionVal, boxSizingReliableVal,
		reliableHiddenOffsetsVal, reliableMarginRightVal;

	// Setup
	div = document.createElement( "div" );
	div.innerHTML = "  <link/><table></table><a href='/a'>a</a><input type='checkbox'/>";
	a = div.getElementsByTagName( "a" )[ 0 ];
	style = a && a.style;

	// Finish early in limited (non-browser) environments
	if ( !style ) {
		return;
	}

	style.cssText = "float:left;opacity:.5";

	// Support: IE<9
	// Make sure that element opacity exists (as opposed to filter)
	support.opacity = style.opacity === "0.5";

	// Verify style float existence
	// (IE uses styleFloat instead of cssFloat)
	support.cssFloat = !!style.cssFloat;

	div.style.backgroundClip = "content-box";
	div.cloneNode( true ).style.backgroundClip = "";
	support.clearCloneStyle = div.style.backgroundClip === "content-box";

	// Support: Firefox<29, Android 2.3
	// Vendor-prefix box-sizing
	support.boxSizing = style.boxSizing === "" || style.MozBoxSizing === "" ||
		style.WebkitBoxSizing === "";

	jQuery.extend(support, {
		reliableHiddenOffsets: function() {
			if ( reliableHiddenOffsetsVal == null ) {
				computeStyleTests();
			}
			return reliableHiddenOffsetsVal;
		},

		boxSizingReliable: function() {
			if ( boxSizingReliableVal == null ) {
				computeStyleTests();
			}
			return boxSizingReliableVal;
		},

		pixelPosition: function() {
			if ( pixelPositionVal == null ) {
				computeStyleTests();
			}
			return pixelPositionVal;
		},

		// Support: Android 2.3
		reliableMarginRight: function() {
			if ( reliableMarginRightVal == null ) {
				computeStyleTests();
			}
			return reliableMarginRightVal;
		}
	});

	function computeStyleTests() {
		// Minified: var b,c,d,j
		var div, body, container, contents;

		body = document.getElementsByTagName( "body" )[ 0 ];
		if ( !body || !body.style ) {
			// Test fired too early or in an unsupported environment, exit.
			return;
		}

		// Setup
		div = document.createElement( "div" );
		container = document.createElement( "div" );
		container.style.cssText = "position:absolute;border:0;width:0;height:0;top:0;left:-9999px";
		body.appendChild( container ).appendChild( div );

		div.style.cssText =
			// Support: Firefox<29, Android 2.3
			// Vendor-prefix box-sizing
			"-webkit-box-sizing:border-box;-moz-box-sizing:border-box;" +
			"box-sizing:border-box;display:block;margin-top:1%;top:1%;" +
			"border:1px;padding:1px;width:4px;position:absolute";

		// Support: IE<9
		// Assume reasonable values in the absence of getComputedStyle
		pixelPositionVal = boxSizingReliableVal = false;
		reliableMarginRightVal = true;

		// Check for getComputedStyle so that this code is not run in IE<9.
		if ( window.getComputedStyle ) {
			pixelPositionVal = ( window.getComputedStyle( div, null ) || {} ).top !== "1%";
			boxSizingReliableVal =
				( window.getComputedStyle( div, null ) || { width: "4px" } ).width === "4px";

			// Support: Android 2.3
			// Div with explicit width and no margin-right incorrectly
			// gets computed margin-right based on width of container (#3333)
			// WebKit Bug 13343 - getComputedStyle returns wrong value for margin-right
			contents = div.appendChild( document.createElement( "div" ) );

			// Reset CSS: box-sizing; display; margin; border; padding
			contents.style.cssText = div.style.cssText =
				// Support: Firefox<29, Android 2.3
				// Vendor-prefix box-sizing
				"-webkit-box-sizing:content-box;-moz-box-sizing:content-box;" +
				"box-sizing:content-box;display:block;margin:0;border:0;padding:0";
			contents.style.marginRight = contents.style.width = "0";
			div.style.width = "1px";

			reliableMarginRightVal =
				!parseFloat( ( window.getComputedStyle( contents, null ) || {} ).marginRight );
		}

		// Support: IE8
		// Check if table cells still have offsetWidth/Height when they are set
		// to display:none and there are still other visible table cells in a
		// table row; if so, offsetWidth/Height are not reliable for use when
		// determining if an element has been hidden directly using
		// display:none (it is still safe to use offsets if a parent element is
		// hidden; don safety goggles and see bug #4512 for more information).
		div.innerHTML = "<table><tr><td></td><td>t</td></tr></table>";
		contents = div.getElementsByTagName( "td" );
		contents[ 0 ].style.cssText = "margin:0;border:0;padding:0;display:none";
		reliableHiddenOffsetsVal = contents[ 0 ].offsetHeight === 0;
		if ( reliableHiddenOffsetsVal ) {
			contents[ 0 ].style.display = "";
			contents[ 1 ].style.display = "none";
			reliableHiddenOffsetsVal = contents[ 0 ].offsetHeight === 0;
		}

		body.removeChild( container );
	}

})();


// A method for quickly swapping in/out CSS properties to get correct calculations.
jQuery.swap = function( elem, options, callback, args ) {
	var ret, name,
		old = {};

	// Remember the old values, and insert the new ones
	for ( name in options ) {
		old[ name ] = elem.style[ name ];
		elem.style[ name ] = options[ name ];
	}

	ret = callback.apply( elem, args || [] );

	// Revert the old values
	for ( name in options ) {
		elem.style[ name ] = old[ name ];
	}

	return ret;
};


var
		ralpha = /alpha\([^)]*\)/i,
	ropacity = /opacity\s*=\s*([^)]*)/,

	// swappable if display is none or starts with table except "table", "table-cell", or "table-caption"
	// see here for display values: https://developer.mozilla.org/en-US/docs/CSS/display
	rdisplayswap = /^(none|table(?!-c[ea]).+)/,
	rnumsplit = new RegExp( "^(" + pnum + ")(.*)$", "i" ),
	rrelNum = new RegExp( "^([+-])=(" + pnum + ")", "i" ),

	cssShow = { position: "absolute", visibility: "hidden", display: "block" },
	cssNormalTransform = {
		letterSpacing: "0",
		fontWeight: "400"
	},

	cssPrefixes = [ "Webkit", "O", "Moz", "ms" ];


// return a css property mapped to a potentially vendor prefixed property
function vendorPropName( style, name ) {

	// shortcut for names that are not vendor prefixed
	if ( name in style ) {
		return name;
	}

	// check for vendor prefixed names
	var capName = name.charAt(0).toUpperCase() + name.slice(1),
		origName = name,
		i = cssPrefixes.length;

	while ( i-- ) {
		name = cssPrefixes[ i ] + capName;
		if ( name in style ) {
			return name;
		}
	}

	return origName;
}

function showHide( elements, show ) {
	var display, elem, hidden,
		values = [],
		index = 0,
		length = elements.length;

	for ( ; index < length; index++ ) {
		elem = elements[ index ];
		if ( !elem.style ) {
			continue;
		}

		values[ index ] = jQuery._data( elem, "olddisplay" );
		display = elem.style.display;
		if ( show ) {
			// Reset the inline display of this element to learn if it is
			// being hidden by cascaded rules or not
			if ( !values[ index ] && display === "none" ) {
				elem.style.display = "";
			}

			// Set elements which have been overridden with display: none
			// in a stylesheet to whatever the default browser style is
			// for such an element
			if ( elem.style.display === "" && isHidden( elem ) ) {
				values[ index ] = jQuery._data( elem, "olddisplay", defaultDisplay(elem.nodeName) );
			}
		} else {
			hidden = isHidden( elem );

			if ( display && display !== "none" || !hidden ) {
				jQuery._data( elem, "olddisplay", hidden ? display : jQuery.css( elem, "display" ) );
			}
		}
	}

	// Set the display of most of the elements in a second loop
	// to avoid the constant reflow
	for ( index = 0; index < length; index++ ) {
		elem = elements[ index ];
		if ( !elem.style ) {
			continue;
		}
		if ( !show || elem.style.display === "none" || elem.style.display === "" ) {
			elem.style.display = show ? values[ index ] || "" : "none";
		}
	}

	return elements;
}

function setPositiveNumber( elem, value, subtract ) {
	var matches = rnumsplit.exec( value );
	return matches ?
		// Guard against undefined "subtract", e.g., when used as in cssHooks
		Math.max( 0, matches[ 1 ] - ( subtract || 0 ) ) + ( matches[ 2 ] || "px" ) :
		value;
}

function augmentWidthOrHeight( elem, name, extra, isBorderBox, styles ) {
	var i = extra === ( isBorderBox ? "border" : "content" ) ?
		// If we already have the right measurement, avoid augmentation
		4 :
		// Otherwise initialize for horizontal or vertical properties
		name === "width" ? 1 : 0,

		val = 0;

	for ( ; i < 4; i += 2 ) {
		// both box models exclude margin, so add it if we want it
		if ( extra === "margin" ) {
			val += jQuery.css( elem, extra + cssExpand[ i ], true, styles );
		}

		if ( isBorderBox ) {
			// border-box includes padding, so remove it if we want content
			if ( extra === "content" ) {
				val -= jQuery.css( elem, "padding" + cssExpand[ i ], true, styles );
			}

			// at this point, extra isn't border nor margin, so remove border
			if ( extra !== "margin" ) {
				val -= jQuery.css( elem, "border" + cssExpand[ i ] + "Width", true, styles );
			}
		} else {
			// at this point, extra isn't content, so add padding
			val += jQuery.css( elem, "padding" + cssExpand[ i ], true, styles );

			// at this point, extra isn't content nor padding, so add border
			if ( extra !== "padding" ) {
				val += jQuery.css( elem, "border" + cssExpand[ i ] + "Width", true, styles );
			}
		}
	}

	return val;
}

function getWidthOrHeight( elem, name, extra ) {

	// Start with offset property, which is equivalent to the border-box value
	var valueIsBorderBox = true,
		val = name === "width" ? elem.offsetWidth : elem.offsetHeight,
		styles = getStyles( elem ),
		isBorderBox = support.boxSizing && jQuery.css( elem, "boxSizing", false, styles ) === "border-box";

	// some non-html elements return undefined for offsetWidth, so check for null/undefined
	// svg - https://bugzilla.mozilla.org/show_bug.cgi?id=649285
	// MathML - https://bugzilla.mozilla.org/show_bug.cgi?id=491668
	if ( val <= 0 || val == null ) {
		// Fall back to computed then uncomputed css if necessary
		val = curCSS( elem, name, styles );
		if ( val < 0 || val == null ) {
			val = elem.style[ name ];
		}

		// Computed unit is not pixels. Stop here and return.
		if ( rnumnonpx.test(val) ) {
			return val;
		}

		// we need the check for style in case a browser which returns unreliable values
		// for getComputedStyle silently falls back to the reliable elem.style
		valueIsBorderBox = isBorderBox && ( support.boxSizingReliable() || val === elem.style[ name ] );

		// Normalize "", auto, and prepare for extra
		val = parseFloat( val ) || 0;
	}

	// use the active box-sizing model to add/subtract irrelevant styles
	return ( val +
		augmentWidthOrHeight(
			elem,
			name,
			extra || ( isBorderBox ? "border" : "content" ),
			valueIsBorderBox,
			styles
		)
	) + "px";
}

jQuery.extend({
	// Add in style property hooks for overriding the default
	// behavior of getting and setting a style property
	cssHooks: {
		opacity: {
			get: function( elem, computed ) {
				if ( computed ) {
					// We should always get a number back from opacity
					var ret = curCSS( elem, "opacity" );
					return ret === "" ? "1" : ret;
				}
			}
		}
	},

	// Don't automatically add "px" to these possibly-unitless properties
	cssNumber: {
		"columnCount": true,
		"fillOpacity": true,
		"flexGrow": true,
		"flexShrink": true,
		"fontWeight": true,
		"lineHeight": true,
		"opacity": true,
		"order": true,
		"orphans": true,
		"widows": true,
		"zIndex": true,
		"zoom": true
	},

	// Add in properties whose names you wish to fix before
	// setting or getting the value
	cssProps: {
		// normalize float css property
		"float": support.cssFloat ? "cssFloat" : "styleFloat"
	},

	// Get and set the style property on a DOM Node
	style: function( elem, name, value, extra ) {
		// Don't set styles on text and comment nodes
		if ( !elem || elem.nodeType === 3 || elem.nodeType === 8 || !elem.style ) {
			return;
		}

		// Make sure that we're working with the right name
		var ret, type, hooks,
			origName = jQuery.camelCase( name ),
			style = elem.style;

		name = jQuery.cssProps[ origName ] || ( jQuery.cssProps[ origName ] = vendorPropName( style, origName ) );

		// gets hook for the prefixed version
		// followed by the unprefixed version
		hooks = jQuery.cssHooks[ name ] || jQuery.cssHooks[ origName ];

		// Check if we're setting a value
		if ( value !== undefined ) {
			type = typeof value;

			// convert relative number strings (+= or -=) to relative numbers. #7345
			if ( type === "string" && (ret = rrelNum.exec( value )) ) {
				value = ( ret[1] + 1 ) * ret[2] + parseFloat( jQuery.css( elem, name ) );
				// Fixes bug #9237
				type = "number";
			}

			// Make sure that null and NaN values aren't set. See: #7116
			if ( value == null || value !== value ) {
				return;
			}

			// If a number was passed in, add 'px' to the (except for certain CSS properties)
			if ( type === "number" && !jQuery.cssNumber[ origName ] ) {
				value += "px";
			}

			// Fixes #8908, it can be done more correctly by specifing setters in cssHooks,
			// but it would mean to define eight (for every problematic property) identical functions
			if ( !support.clearCloneStyle && value === "" && name.indexOf("background") === 0 ) {
				style[ name ] = "inherit";
			}

			// If a hook was provided, use that value, otherwise just set the specified value
			if ( !hooks || !("set" in hooks) || (value = hooks.set( elem, value, extra )) !== undefined ) {

				// Support: IE
				// Swallow errors from 'invalid' CSS values (#5509)
				try {
					style[ name ] = value;
				} catch(e) {}
			}

		} else {
			// If a hook was provided get the non-computed value from there
			if ( hooks && "get" in hooks && (ret = hooks.get( elem, false, extra )) !== undefined ) {
				return ret;
			}

			// Otherwise just get the value from the style object
			return style[ name ];
		}
	},

	css: function( elem, name, extra, styles ) {
		var num, val, hooks,
			origName = jQuery.camelCase( name );

		// Make sure that we're working with the right name
		name = jQuery.cssProps[ origName ] || ( jQuery.cssProps[ origName ] = vendorPropName( elem.style, origName ) );

		// gets hook for the prefixed version
		// followed by the unprefixed version
		hooks = jQuery.cssHooks[ name ] || jQuery.cssHooks[ origName ];

		// If a hook was provided get the computed value from there
		if ( hooks && "get" in hooks ) {
			val = hooks.get( elem, true, extra );
		}

		// Otherwise, if a way to get the computed value exists, use that
		if ( val === undefined ) {
			val = curCSS( elem, name, styles );
		}

		//convert "normal" to computed value
		if ( val === "normal" && name in cssNormalTransform ) {
			val = cssNormalTransform[ name ];
		}

		// Return, converting to number if forced or a qualifier was provided and val looks numeric
		if ( extra === "" || extra ) {
			num = parseFloat( val );
			return extra === true || jQuery.isNumeric( num ) ? num || 0 : val;
		}
		return val;
	}
});

jQuery.each([ "height", "width" ], function( i, name ) {
	jQuery.cssHooks[ name ] = {
		get: function( elem, computed, extra ) {
			if ( computed ) {
				// certain elements can have dimension info if we invisibly show them
				// however, it must have a current display style that would benefit from this
				return rdisplayswap.test( jQuery.css( elem, "display" ) ) && elem.offsetWidth === 0 ?
					jQuery.swap( elem, cssShow, function() {
						return getWidthOrHeight( elem, name, extra );
					}) :
					getWidthOrHeight( elem, name, extra );
			}
		},

		set: function( elem, value, extra ) {
			var styles = extra && getStyles( elem );
			return setPositiveNumber( elem, value, extra ?
				augmentWidthOrHeight(
					elem,
					name,
					extra,
					support.boxSizing && jQuery.css( elem, "boxSizing", false, styles ) === "border-box",
					styles
				) : 0
			);
		}
	};
});

if ( !support.opacity ) {
	jQuery.cssHooks.opacity = {
		get: function( elem, computed ) {
			// IE uses filters for opacity
			return ropacity.test( (computed && elem.currentStyle ? elem.currentStyle.filter : elem.style.filter) || "" ) ?
				( 0.01 * parseFloat( RegExp.$1 ) ) + "" :
				computed ? "1" : "";
		},

		set: function( elem, value ) {
			var style = elem.style,
				currentStyle = elem.currentStyle,
				opacity = jQuery.isNumeric( value ) ? "alpha(opacity=" + value * 100 + ")" : "",
				filter = currentStyle && currentStyle.filter || style.filter || "";

			// IE has trouble with opacity if it does not have layout
			// Force it by setting the zoom level
			style.zoom = 1;

			// if setting opacity to 1, and no other filters exist - attempt to remove filter attribute #6652
			// if value === "", then remove inline opacity #12685
			if ( ( value >= 1 || value === "" ) &&
					jQuery.trim( filter.replace( ralpha, "" ) ) === "" &&
					style.removeAttribute ) {

				// Setting style.filter to null, "" & " " still leave "filter:" in the cssText
				// if "filter:" is present at all, clearType is disabled, we want to avoid this
				// style.removeAttribute is IE Only, but so apparently is this code path...
				style.removeAttribute( "filter" );

				// if there is no filter style applied in a css rule or unset inline opacity, we are done
				if ( value === "" || currentStyle && !currentStyle.filter ) {
					return;
				}
			}

			// otherwise, set new filter values
			style.filter = ralpha.test( filter ) ?
				filter.replace( ralpha, opacity ) :
				filter + " " + opacity;
		}
	};
}

jQuery.cssHooks.marginRight = addGetHookIf( support.reliableMarginRight,
	function( elem, computed ) {
		if ( computed ) {
			// WebKit Bug 13343 - getComputedStyle returns wrong value for margin-right
			// Work around by temporarily setting element display to inline-block
			return jQuery.swap( elem, { "display": "inline-block" },
				curCSS, [ elem, "marginRight" ] );
		}
	}
);

// These hooks are used by animate to expand properties
jQuery.each({
	margin: "",
	padding: "",
	border: "Width"
}, function( prefix, suffix ) {
	jQuery.cssHooks[ prefix + suffix ] = {
		expand: function( value ) {
			var i = 0,
				expanded = {},

				// assumes a single number if not a string
				parts = typeof value === "string" ? value.split(" ") : [ value ];

			for ( ; i < 4; i++ ) {
				expanded[ prefix + cssExpand[ i ] + suffix ] =
					parts[ i ] || parts[ i - 2 ] || parts[ 0 ];
			}

			return expanded;
		}
	};

	if ( !rmargin.test( prefix ) ) {
		jQuery.cssHooks[ prefix + suffix ].set = setPositiveNumber;
	}
});

jQuery.fn.extend({
	css: function( name, value ) {
		return access( this, function( elem, name, value ) {
			var styles, len,
				map = {},
				i = 0;

			if ( jQuery.isArray( name ) ) {
				styles = getStyles( elem );
				len = name.length;

				for ( ; i < len; i++ ) {
					map[ name[ i ] ] = jQuery.css( elem, name[ i ], false, styles );
				}

				return map;
			}

			return value !== undefined ?
				jQuery.style( elem, name, value ) :
				jQuery.css( elem, name );
		}, name, value, arguments.length > 1 );
	},
	show: function() {
		return showHide( this, true );
	},
	hide: function() {
		return showHide( this );
	},
	toggle: function( state ) {
		if ( typeof state === "boolean" ) {
			return state ? this.show() : this.hide();
		}

		return this.each(function() {
			if ( isHidden( this ) ) {
				jQuery( this ).show();
			} else {
				jQuery( this ).hide();
			}
		});
	}
});


function Tween( elem, options, prop, end, easing ) {
	return new Tween.prototype.init( elem, options, prop, end, easing );
}
jQuery.Tween = Tween;

Tween.prototype = {
	constructor: Tween,
	init: function( elem, options, prop, end, easing, unit ) {
		this.elem = elem;
		this.prop = prop;
		this.easing = easing || "swing";
		this.options = options;
		this.start = this.now = this.cur();
		this.end = end;
		this.unit = unit || ( jQuery.cssNumber[ prop ] ? "" : "px" );
	},
	cur: function() {
		var hooks = Tween.propHooks[ this.prop ];

		return hooks && hooks.get ?
			hooks.get( this ) :
			Tween.propHooks._default.get( this );
	},
	run: function( percent ) {
		var eased,
			hooks = Tween.propHooks[ this.prop ];

		if ( this.options.duration ) {
			this.pos = eased = jQuery.easing[ this.easing ](
				percent, this.options.duration * percent, 0, 1, this.options.duration
			);
		} else {
			this.pos = eased = percent;
		}
		this.now = ( this.end - this.start ) * eased + this.start;

		if ( this.options.step ) {
			this.options.step.call( this.elem, this.now, this );
		}

		if ( hooks && hooks.set ) {
			hooks.set( this );
		} else {
			Tween.propHooks._default.set( this );
		}
		return this;
	}
};

Tween.prototype.init.prototype = Tween.prototype;

Tween.propHooks = {
	_default: {
		get: function( tween ) {
			var result;

			if ( tween.elem[ tween.prop ] != null &&
				(!tween.elem.style || tween.elem.style[ tween.prop ] == null) ) {
				return tween.elem[ tween.prop ];
			}

			// passing an empty string as a 3rd parameter to .css will automatically
			// attempt a parseFloat and fallback to a string if the parse fails
			// so, simple values such as "10px" are parsed to Float.
			// complex values such as "rotate(1rad)" are returned as is.
			result = jQuery.css( tween.elem, tween.prop, "" );
			// Empty strings, null, undefined and "auto" are converted to 0.
			return !result || result === "auto" ? 0 : result;
		},
		set: function( tween ) {
			// use step hook for back compat - use cssHook if its there - use .style if its
			// available and use plain properties where available
			if ( jQuery.fx.step[ tween.prop ] ) {
				jQuery.fx.step[ tween.prop ]( tween );
			} else if ( tween.elem.style && ( tween.elem.style[ jQuery.cssProps[ tween.prop ] ] != null || jQuery.cssHooks[ tween.prop ] ) ) {
				jQuery.style( tween.elem, tween.prop, tween.now + tween.unit );
			} else {
				tween.elem[ tween.prop ] = tween.now;
			}
		}
	}
};

// Support: IE <=9
// Panic based approach to setting things on disconnected nodes

Tween.propHooks.scrollTop = Tween.propHooks.scrollLeft = {
	set: function( tween ) {
		if ( tween.elem.nodeType && tween.elem.parentNode ) {
			tween.elem[ tween.prop ] = tween.now;
		}
	}
};

jQuery.easing = {
	linear: function( p ) {
		return p;
	},
	swing: function( p ) {
		return 0.5 - Math.cos( p * Math.PI ) / 2;
	}
};

jQuery.fx = Tween.prototype.init;

// Back Compat <1.8 extension point
jQuery.fx.step = {};




var
	fxNow, timerId,
	rfxtypes = /^(?:toggle|show|hide)$/,
	rfxnum = new RegExp( "^(?:([+-])=|)(" + pnum + ")([a-z%]*)$", "i" ),
	rrun = /queueHooks$/,
	animationPrefilters = [ defaultPrefilter ],
	tweeners = {
		"*": [ function( prop, value ) {
			var tween = this.createTween( prop, value ),
				target = tween.cur(),
				parts = rfxnum.exec( value ),
				unit = parts && parts[ 3 ] || ( jQuery.cssNumber[ prop ] ? "" : "px" ),

				// Starting value computation is required for potential unit mismatches
				start = ( jQuery.cssNumber[ prop ] || unit !== "px" && +target ) &&
					rfxnum.exec( jQuery.css( tween.elem, prop ) ),
				scale = 1,
				maxIterations = 20;

			if ( start && start[ 3 ] !== unit ) {
				// Trust units reported by jQuery.css
				unit = unit || start[ 3 ];

				// Make sure we update the tween properties later on
				parts = parts || [];

				// Iteratively approximate from a nonzero starting point
				start = +target || 1;

				do {
					// If previous iteration zeroed out, double until we get *something*
					// Use a string for doubling factor so we don't accidentally see scale as unchanged below
					scale = scale || ".5";

					// Adjust and apply
					start = start / scale;
					jQuery.style( tween.elem, prop, start + unit );

				// Update scale, tolerating zero or NaN from tween.cur()
				// And breaking the loop if scale is unchanged or perfect, or if we've just had enough
				} while ( scale !== (scale = tween.cur() / target) && scale !== 1 && --maxIterations );
			}

			// Update tween properties
			if ( parts ) {
				start = tween.start = +start || +target || 0;
				tween.unit = unit;
				// If a +=/-= token was provided, we're doing a relative animation
				tween.end = parts[ 1 ] ?
					start + ( parts[ 1 ] + 1 ) * parts[ 2 ] :
					+parts[ 2 ];
			}

			return tween;
		} ]
	};

// Animations created synchronously will run synchronously
function createFxNow() {
	setTimeout(function() {
		fxNow = undefined;
	});
	return ( fxNow = jQuery.now() );
}

// Generate parameters to create a standard animation
function genFx( type, includeWidth ) {
	var which,
		attrs = { height: type },
		i = 0;

	// if we include width, step value is 1 to do all cssExpand values,
	// if we don't include width, step value is 2 to skip over Left and Right
	includeWidth = includeWidth ? 1 : 0;
	for ( ; i < 4 ; i += 2 - includeWidth ) {
		which = cssExpand[ i ];
		attrs[ "margin" + which ] = attrs[ "padding" + which ] = type;
	}

	if ( includeWidth ) {
		attrs.opacity = attrs.width = type;
	}

	return attrs;
}

function createTween( value, prop, animation ) {
	var tween,
		collection = ( tweeners[ prop ] || [] ).concat( tweeners[ "*" ] ),
		index = 0,
		length = collection.length;
	for ( ; index < length; index++ ) {
		if ( (tween = collection[ index ].call( animation, prop, value )) ) {

			// we're done with this property
			return tween;
		}
	}
}

function defaultPrefilter( elem, props, opts ) {
	/* jshint validthis: true */
	var prop, value, toggle, tween, hooks, oldfire, display, checkDisplay,
		anim = this,
		orig = {},
		style = elem.style,
		hidden = elem.nodeType && isHidden( elem ),
		dataShow = jQuery._data( elem, "fxshow" );

	// handle queue: false promises
	if ( !opts.queue ) {
		hooks = jQuery._queueHooks( elem, "fx" );
		if ( hooks.unqueued == null ) {
			hooks.unqueued = 0;
			oldfire = hooks.empty.fire;
			hooks.empty.fire = function() {
				if ( !hooks.unqueued ) {
					oldfire();
				}
			};
		}
		hooks.unqueued++;

		anim.always(function() {
			// doing this makes sure that the complete handler will be called
			// before this completes
			anim.always(function() {
				hooks.unqueued--;
				if ( !jQuery.queue( elem, "fx" ).length ) {
					hooks.empty.fire();
				}
			});
		});
	}

	// height/width overflow pass
	if ( elem.nodeType === 1 && ( "height" in props || "width" in props ) ) {
		// Make sure that nothing sneaks out
		// Record all 3 overflow attributes because IE does not
		// change the overflow attribute when overflowX and
		// overflowY are set to the same value
		opts.overflow = [ style.overflow, style.overflowX, style.overflowY ];

		// Set display property to inline-block for height/width
		// animations on inline elements that are having width/height animated
		display = jQuery.css( elem, "display" );

		// Test default display if display is currently "none"
		checkDisplay = display === "none" ?
			jQuery._data( elem, "olddisplay" ) || defaultDisplay( elem.nodeName ) : display;

		if ( checkDisplay === "inline" && jQuery.css( elem, "float" ) === "none" ) {

			// inline-level elements accept inline-block;
			// block-level elements need to be inline with layout
			if ( !support.inlineBlockNeedsLayout || defaultDisplay( elem.nodeName ) === "inline" ) {
				style.display = "inline-block";
			} else {
				style.zoom = 1;
			}
		}
	}

	if ( opts.overflow ) {
		style.overflow = "hidden";
		if ( !support.shrinkWrapBlocks() ) {
			anim.always(function() {
				style.overflow = opts.overflow[ 0 ];
				style.overflowX = opts.overflow[ 1 ];
				style.overflowY = opts.overflow[ 2 ];
			});
		}
	}

	// show/hide pass
	for ( prop in props ) {
		value = props[ prop ];
		if ( rfxtypes.exec( value ) ) {
			delete props[ prop ];
			toggle = toggle || value === "toggle";
			if ( value === ( hidden ? "hide" : "show" ) ) {

				// If there is dataShow left over from a stopped hide or show and we are going to proceed with show, we should pretend to be hidden
				if ( value === "show" && dataShow && dataShow[ prop ] !== undefined ) {
					hidden = true;
				} else {
					continue;
				}
			}
			orig[ prop ] = dataShow && dataShow[ prop ] || jQuery.style( elem, prop );

		// Any non-fx value stops us from restoring the original display value
		} else {
			display = undefined;
		}
	}

	if ( !jQuery.isEmptyObject( orig ) ) {
		if ( dataShow ) {
			if ( "hidden" in dataShow ) {
				hidden = dataShow.hidden;
			}
		} else {
			dataShow = jQuery._data( elem, "fxshow", {} );
		}

		// store state if its toggle - enables .stop().toggle() to "reverse"
		if ( toggle ) {
			dataShow.hidden = !hidden;
		}
		if ( hidden ) {
			jQuery( elem ).show();
		} else {
			anim.done(function() {
				jQuery( elem ).hide();
			});
		}
		anim.done(function() {
			var prop;
			jQuery._removeData( elem, "fxshow" );
			for ( prop in orig ) {
				jQuery.style( elem, prop, orig[ prop ] );
			}
		});
		for ( prop in orig ) {
			tween = createTween( hidden ? dataShow[ prop ] : 0, prop, anim );

			if ( !( prop in dataShow ) ) {
				dataShow[ prop ] = tween.start;
				if ( hidden ) {
					tween.end = tween.start;
					tween.start = prop === "width" || prop === "height" ? 1 : 0;
				}
			}
		}

	// If this is a noop like .hide().hide(), restore an overwritten display value
	} else if ( (display === "none" ? defaultDisplay( elem.nodeName ) : display) === "inline" ) {
		style.display = display;
	}
}

function propFilter( props, specialEasing ) {
	var index, name, easing, value, hooks;

	// camelCase, specialEasing and expand cssHook pass
	for ( index in props ) {
		name = jQuery.camelCase( index );
		easing = specialEasing[ name ];
		value = props[ index ];
		if ( jQuery.isArray( value ) ) {
			easing = value[ 1 ];
			value = props[ index ] = value[ 0 ];
		}

		if ( index !== name ) {
			props[ name ] = value;
			delete props[ index ];
		}

		hooks = jQuery.cssHooks[ name ];
		if ( hooks && "expand" in hooks ) {
			value = hooks.expand( value );
			delete props[ name ];

			// not quite $.extend, this wont overwrite keys already present.
			// also - reusing 'index' from above because we have the correct "name"
			for ( index in value ) {
				if ( !( index in props ) ) {
					props[ index ] = value[ index ];
					specialEasing[ index ] = easing;
				}
			}
		} else {
			specialEasing[ name ] = easing;
		}
	}
}

function Animation( elem, properties, options ) {
	var result,
		stopped,
		index = 0,
		length = animationPrefilters.length,
		deferred = jQuery.Deferred().always( function() {
			// don't match elem in the :animated selector
			delete tick.elem;
		}),
		tick = function() {
			if ( stopped ) {
				return false;
			}
			var currentTime = fxNow || createFxNow(),
				remaining = Math.max( 0, animation.startTime + animation.duration - currentTime ),
				// archaic crash bug won't allow us to use 1 - ( 0.5 || 0 ) (#12497)
				temp = remaining / animation.duration || 0,
				percent = 1 - temp,
				index = 0,
				length = animation.tweens.length;

			for ( ; index < length ; index++ ) {
				animation.tweens[ index ].run( percent );
			}

			deferred.notifyWith( elem, [ animation, percent, remaining ]);

			if ( percent < 1 && length ) {
				return remaining;
			} else {
				deferred.resolveWith( elem, [ animation ] );
				return false;
			}
		},
		animation = deferred.promise({
			elem: elem,
			props: jQuery.extend( {}, properties ),
			opts: jQuery.extend( true, { specialEasing: {} }, options ),
			originalProperties: properties,
			originalOptions: options,
			startTime: fxNow || createFxNow(),
			duration: options.duration,
			tweens: [],
			createTween: function( prop, end ) {
				var tween = jQuery.Tween( elem, animation.opts, prop, end,
						animation.opts.specialEasing[ prop ] || animation.opts.easing );
				animation.tweens.push( tween );
				return tween;
			},
			stop: function( gotoEnd ) {
				var index = 0,
					// if we are going to the end, we want to run all the tweens
					// otherwise we skip this part
					length = gotoEnd ? animation.tweens.length : 0;
				if ( stopped ) {
					return this;
				}
				stopped = true;
				for ( ; index < length ; index++ ) {
					animation.tweens[ index ].run( 1 );
				}

				// resolve when we played the last frame
				// otherwise, reject
				if ( gotoEnd ) {
					deferred.resolveWith( elem, [ animation, gotoEnd ] );
				} else {
					deferred.rejectWith( elem, [ animation, gotoEnd ] );
				}
				return this;
			}
		}),
		props = animation.props;

	propFilter( props, animation.opts.specialEasing );

	for ( ; index < length ; index++ ) {
		result = animationPrefilters[ index ].call( animation, elem, props, animation.opts );
		if ( result ) {
			return result;
		}
	}

	jQuery.map( props, createTween, animation );

	if ( jQuery.isFunction( animation.opts.start ) ) {
		animation.opts.start.call( elem, animation );
	}

	jQuery.fx.timer(
		jQuery.extend( tick, {
			elem: elem,
			anim: animation,
			queue: animation.opts.queue
		})
	);

	// attach callbacks from options
	return animation.progress( animation.opts.progress )
		.done( animation.opts.done, animation.opts.complete )
		.fail( animation.opts.fail )
		.always( animation.opts.always );
}

jQuery.Animation = jQuery.extend( Animation, {
	tweener: function( props, callback ) {
		if ( jQuery.isFunction( props ) ) {
			callback = props;
			props = [ "*" ];
		} else {
			props = props.split(" ");
		}

		var prop,
			index = 0,
			length = props.length;

		for ( ; index < length ; index++ ) {
			prop = props[ index ];
			tweeners[ prop ] = tweeners[ prop ] || [];
			tweeners[ prop ].unshift( callback );
		}
	},

	prefilter: function( callback, prepend ) {
		if ( prepend ) {
			animationPrefilters.unshift( callback );
		} else {
			animationPrefilters.push( callback );
		}
	}
});

jQuery.speed = function( speed, easing, fn ) {
	var opt = speed && typeof speed === "object" ? jQuery.extend( {}, speed ) : {
		complete: fn || !fn && easing ||
			jQuery.isFunction( speed ) && speed,
		duration: speed,
		easing: fn && easing || easing && !jQuery.isFunction( easing ) && easing
	};

	opt.duration = jQuery.fx.off ? 0 : typeof opt.duration === "number" ? opt.duration :
		opt.duration in jQuery.fx.speeds ? jQuery.fx.speeds[ opt.duration ] : jQuery.fx.speeds._default;

	// normalize opt.queue - true/undefined/null -> "fx"
	if ( opt.queue == null || opt.queue === true ) {
		opt.queue = "fx";
	}

	// Queueing
	opt.old = opt.complete;

	opt.complete = function() {
		if ( jQuery.isFunction( opt.old ) ) {
			opt.old.call( this );
		}

		if ( opt.queue ) {
			jQuery.dequeue( this, opt.queue );
		}
	};

	return opt;
};

jQuery.fn.extend({
	fadeTo: function( speed, to, easing, callback ) {

		// show any hidden elements after setting opacity to 0
		return this.filter( isHidden ).css( "opacity", 0 ).show()

			// animate to the value specified
			.end().animate({ opacity: to }, speed, easing, callback );
	},
	animate: function( prop, speed, easing, callback ) {
		var empty = jQuery.isEmptyObject( prop ),
			optall = jQuery.speed( speed, easing, callback ),
			doAnimation = function() {
				// Operate on a copy of prop so per-property easing won't be lost
				var anim = Animation( this, jQuery.extend( {}, prop ), optall );

				// Empty animations, or finishing resolves immediately
				if ( empty || jQuery._data( this, "finish" ) ) {
					anim.stop( true );
				}
			};
			doAnimation.finish = doAnimation;

		return empty || optall.queue === false ?
			this.each( doAnimation ) :
			this.queue( optall.queue, doAnimation );
	},
	stop: function( type, clearQueue, gotoEnd ) {
		var stopQueue = function( hooks ) {
			var stop = hooks.stop;
			delete hooks.stop;
			stop( gotoEnd );
		};

		if ( typeof type !== "string" ) {
			gotoEnd = clearQueue;
			clearQueue = type;
			type = undefined;
		}
		if ( clearQueue && type !== false ) {
			this.queue( type || "fx", [] );
		}

		return this.each(function() {
			var dequeue = true,
				index = type != null && type + "queueHooks",
				timers = jQuery.timers,
				data = jQuery._data( this );

			if ( index ) {
				if ( data[ index ] && data[ index ].stop ) {
					stopQueue( data[ index ] );
				}
			} else {
				for ( index in data ) {
					if ( data[ index ] && data[ index ].stop && rrun.test( index ) ) {
						stopQueue( data[ index ] );
					}
				}
			}

			for ( index = timers.length; index--; ) {
				if ( timers[ index ].elem === this && (type == null || timers[ index ].queue === type) ) {
					timers[ index ].anim.stop( gotoEnd );
					dequeue = false;
					timers.splice( index, 1 );
				}
			}

			// start the next in the queue if the last step wasn't forced
			// timers currently will call their complete callbacks, which will dequeue
			// but only if they were gotoEnd
			if ( dequeue || !gotoEnd ) {
				jQuery.dequeue( this, type );
			}
		});
	},
	finish: function( type ) {
		if ( type !== false ) {
			type = type || "fx";
		}
		return this.each(function() {
			var index,
				data = jQuery._data( this ),
				queue = data[ type + "queue" ],
				hooks = data[ type + "queueHooks" ],
				timers = jQuery.timers,
				length = queue ? queue.length : 0;

			// enable finishing flag on private data
			data.finish = true;

			// empty the queue first
			jQuery.queue( this, type, [] );

			if ( hooks && hooks.stop ) {
				hooks.stop.call( this, true );
			}

			// look for any active animations, and finish them
			for ( index = timers.length; index--; ) {
				if ( timers[ index ].elem === this && timers[ index ].queue === type ) {
					timers[ index ].anim.stop( true );
					timers.splice( index, 1 );
				}
			}

			// look for any animations in the old queue and finish them
			for ( index = 0; index < length; index++ ) {
				if ( queue[ index ] && queue[ index ].finish ) {
					queue[ index ].finish.call( this );
				}
			}

			// turn off finishing flag
			delete data.finish;
		});
	}
});

jQuery.each([ "toggle", "show", "hide" ], function( i, name ) {
	var cssFn = jQuery.fn[ name ];
	jQuery.fn[ name ] = function( speed, easing, callback ) {
		return speed == null || typeof speed === "boolean" ?
			cssFn.apply( this, arguments ) :
			this.animate( genFx( name, true ), speed, easing, callback );
	};
});

// Generate shortcuts for custom animations
jQuery.each({
	slideDown: genFx("show"),
	slideUp: genFx("hide"),
	slideToggle: genFx("toggle"),
	fadeIn: { opacity: "show" },
	fadeOut: { opacity: "hide" },
	fadeToggle: { opacity: "toggle" }
}, function( name, props ) {
	jQuery.fn[ name ] = function( speed, easing, callback ) {
		return this.animate( props, speed, easing, callback );
	};
});

jQuery.timers = [];
jQuery.fx.tick = function() {
	var timer,
		timers = jQuery.timers,
		i = 0;

	fxNow = jQuery.now();

	for ( ; i < timers.length; i++ ) {
		timer = timers[ i ];
		// Checks the timer has not already been removed
		if ( !timer() && timers[ i ] === timer ) {
			timers.splice( i--, 1 );
		}
	}

	if ( !timers.length ) {
		jQuery.fx.stop();
	}
	fxNow = undefined;
};

jQuery.fx.timer = function( timer ) {
	jQuery.timers.push( timer );
	if ( timer() ) {
		jQuery.fx.start();
	} else {
		jQuery.timers.pop();
	}
};

jQuery.fx.interval = 13;

jQuery.fx.start = function() {
	if ( !timerId ) {
		timerId = setInterval( jQuery.fx.tick, jQuery.fx.interval );
	}
};

jQuery.fx.stop = function() {
	clearInterval( timerId );
	timerId = null;
};

jQuery.fx.speeds = {
	slow: 600,
	fast: 200,
	// Default speed
	_default: 400
};


// Based off of the plugin by Clint Helfers, with permission.
// http://blindsignals.com/index.php/2009/07/jquery-delay/
jQuery.fn.delay = function( time, type ) {
	time = jQuery.fx ? jQuery.fx.speeds[ time ] || time : time;
	type = type || "fx";

	return this.queue( type, function( next, hooks ) {
		var timeout = setTimeout( next, time );
		hooks.stop = function() {
			clearTimeout( timeout );
		};
	});
};


(function() {
	// Minified: var a,b,c,d,e
	var input, div, select, a, opt;

	// Setup
	div = document.createElement( "div" );
	div.setAttribute( "className", "t" );
	div.innerHTML = "  <link/><table></table><a href='/a'>a</a><input type='checkbox'/>";
	a = div.getElementsByTagName("a")[ 0 ];

	// First batch of tests.
	select = document.createElement("select");
	opt = select.appendChild( document.createElement("option") );
	input = div.getElementsByTagName("input")[ 0 ];

	a.style.cssText = "top:1px";

	// Test setAttribute on camelCase class. If it works, we need attrFixes when doing get/setAttribute (ie6/7)
	support.getSetAttribute = div.className !== "t";

	// Get the style information from getAttribute
	// (IE uses .cssText instead)
	support.style = /top/.test( a.getAttribute("style") );

	// Make sure that URLs aren't manipulated
	// (IE normalizes it by default)
	support.hrefNormalized = a.getAttribute("href") === "/a";

	// Check the default checkbox/radio value ("" on WebKit; "on" elsewhere)
	support.checkOn = !!input.value;

	// Make sure that a selected-by-default option has a working selected property.
	// (WebKit defaults to false instead of true, IE too, if it's in an optgroup)
	support.optSelected = opt.selected;

	// Tests for enctype support on a form (#6743)
	support.enctype = !!document.createElement("form").enctype;

	// Make sure that the options inside disabled selects aren't marked as disabled
	// (WebKit marks them as disabled)
	select.disabled = true;
	support.optDisabled = !opt.disabled;

	// Support: IE8 only
	// Check if we can trust getAttribute("value")
	input = document.createElement( "input" );
	input.setAttribute( "value", "" );
	support.input = input.getAttribute( "value" ) === "";

	// Check if an input maintains its value after becoming a radio
	input.value = "t";
	input.setAttribute( "type", "radio" );
	support.radioValue = input.value === "t";
})();


var rreturn = /\r/g;

jQuery.fn.extend({
	val: function( value ) {
		var hooks, ret, isFunction,
			elem = this[0];

		if ( !arguments.length ) {
			if ( elem ) {
				hooks = jQuery.valHooks[ elem.type ] || jQuery.valHooks[ elem.nodeName.toLowerCase() ];

				if ( hooks && "get" in hooks && (ret = hooks.get( elem, "value" )) !== undefined ) {
					return ret;
				}

				ret = elem.value;

				return typeof ret === "string" ?
					// handle most common string cases
					ret.replace(rreturn, "") :
					// handle cases where value is null/undef or number
					ret == null ? "" : ret;
			}

			return;
		}

		isFunction = jQuery.isFunction( value );

		return this.each(function( i ) {
			var val;

			if ( this.nodeType !== 1 ) {
				return;
			}

			if ( isFunction ) {
				val = value.call( this, i, jQuery( this ).val() );
			} else {
				val = value;
			}

			// Treat null/undefined as ""; convert numbers to string
			if ( val == null ) {
				val = "";
			} else if ( typeof val === "number" ) {
				val += "";
			} else if ( jQuery.isArray( val ) ) {
				val = jQuery.map( val, function( value ) {
					return value == null ? "" : value + "";
				});
			}

			hooks = jQuery.valHooks[ this.type ] || jQuery.valHooks[ this.nodeName.toLowerCase() ];

			// If set returns undefined, fall back to normal setting
			if ( !hooks || !("set" in hooks) || hooks.set( this, val, "value" ) === undefined ) {
				this.value = val;
			}
		});
	}
});

jQuery.extend({
	valHooks: {
		option: {
			get: function( elem ) {
				var val = jQuery.find.attr( elem, "value" );
				return val != null ?
					val :
					// Support: IE10-11+
					// option.text throws exceptions (#14686, #14858)
					jQuery.trim( jQuery.text( elem ) );
			}
		},
		select: {
			get: function( elem ) {
				var value, option,
					options = elem.options,
					index = elem.selectedIndex,
					one = elem.type === "select-one" || index < 0,
					values = one ? null : [],
					max = one ? index + 1 : options.length,
					i = index < 0 ?
						max :
						one ? index : 0;

				// Loop through all the selected options
				for ( ; i < max; i++ ) {
					option = options[ i ];

					// oldIE doesn't update selected after form reset (#2551)
					if ( ( option.selected || i === index ) &&
							// Don't return options that are disabled or in a disabled optgroup
							( support.optDisabled ? !option.disabled : option.getAttribute("disabled") === null ) &&
							( !option.parentNode.disabled || !jQuery.nodeName( option.parentNode, "optgroup" ) ) ) {

						// Get the specific value for the option
						value = jQuery( option ).val();

						// We don't need an array for one selects
						if ( one ) {
							return value;
						}

						// Multi-Selects return an array
						values.push( value );
					}
				}

				return values;
			},

			set: function( elem, value ) {
				var optionSet, option,
					options = elem.options,
					values = jQuery.makeArray( value ),
					i = options.length;

				while ( i-- ) {
					option = options[ i ];

					if ( jQuery.inArray( jQuery.valHooks.option.get( option ), values ) >= 0 ) {

						// Support: IE6
						// When new option element is added to select box we need to
						// force reflow of newly added node in order to workaround delay
						// of initialization properties
						try {
							option.selected = optionSet = true;

						} catch ( _ ) {

							// Will be executed only in IE6
							option.scrollHeight;
						}

					} else {
						option.selected = false;
					}
				}

				// Force browsers to behave consistently when non-matching value is set
				if ( !optionSet ) {
					elem.selectedIndex = -1;
				}

				return options;
			}
		}
	}
});

// Radios and checkboxes getter/setter
jQuery.each([ "radio", "checkbox" ], function() {
	jQuery.valHooks[ this ] = {
		set: function( elem, value ) {
			if ( jQuery.isArray( value ) ) {
				return ( elem.checked = jQuery.inArray( jQuery(elem).val(), value ) >= 0 );
			}
		}
	};
	if ( !support.checkOn ) {
		jQuery.valHooks[ this ].get = function( elem ) {
			// Support: Webkit
			// "" is returned instead of "on" if a value isn't specified
			return elem.getAttribute("value") === null ? "on" : elem.value;
		};
	}
});




var nodeHook, boolHook,
	attrHandle = jQuery.expr.attrHandle,
	ruseDefault = /^(?:checked|selected)$/i,
	getSetAttribute = support.getSetAttribute,
	getSetInput = support.input;

jQuery.fn.extend({
	attr: function( name, value ) {
		return access( this, jQuery.attr, name, value, arguments.length > 1 );
	},

	removeAttr: function( name ) {
		return this.each(function() {
			jQuery.removeAttr( this, name );
		});
	}
});

jQuery.extend({
	attr: function( elem, name, value ) {
		var hooks, ret,
			nType = elem.nodeType;

		// don't get/set attributes on text, comment and attribute nodes
		if ( !elem || nType === 3 || nType === 8 || nType === 2 ) {
			return;
		}

		// Fallback to prop when attributes are not supported
		if ( typeof elem.getAttribute === strundefined ) {
			return jQuery.prop( elem, name, value );
		}

		// All attributes are lowercase
		// Grab necessary hook if one is defined
		if ( nType !== 1 || !jQuery.isXMLDoc( elem ) ) {
			name = name.toLowerCase();
			hooks = jQuery.attrHooks[ name ] ||
				( jQuery.expr.match.bool.test( name ) ? boolHook : nodeHook );
		}

		if ( value !== undefined ) {

			if ( value === null ) {
				jQuery.removeAttr( elem, name );

			} else if ( hooks && "set" in hooks && (ret = hooks.set( elem, value, name )) !== undefined ) {
				return ret;

			} else {
				elem.setAttribute( name, value + "" );
				return value;
			}

		} else if ( hooks && "get" in hooks && (ret = hooks.get( elem, name )) !== null ) {
			return ret;

		} else {
			ret = jQuery.find.attr( elem, name );

			// Non-existent attributes return null, we normalize to undefined
			return ret == null ?
				undefined :
				ret;
		}
	},

	removeAttr: function( elem, value ) {
		var name, propName,
			i = 0,
			attrNames = value && value.match( rnotwhite );

		if ( attrNames && elem.nodeType === 1 ) {
			while ( (name = attrNames[i++]) ) {
				propName = jQuery.propFix[ name ] || name;

				// Boolean attributes get special treatment (#10870)
				if ( jQuery.expr.match.bool.test( name ) ) {
					// Set corresponding property to false
					if ( getSetInput && getSetAttribute || !ruseDefault.test( name ) ) {
						elem[ propName ] = false;
					// Support: IE<9
					// Also clear defaultChecked/defaultSelected (if appropriate)
					} else {
						elem[ jQuery.camelCase( "default-" + name ) ] =
							elem[ propName ] = false;
					}

				// See #9699 for explanation of this approach (setting first, then removal)
				} else {
					jQuery.attr( elem, name, "" );
				}

				elem.removeAttribute( getSetAttribute ? name : propName );
			}
		}
	},

	attrHooks: {
		type: {
			set: function( elem, value ) {
				if ( !support.radioValue && value === "radio" && jQuery.nodeName(elem, "input") ) {
					// Setting the type on a radio button after the value resets the value in IE6-9
					// Reset value to default in case type is set after value during creation
					var val = elem.value;
					elem.setAttribute( "type", value );
					if ( val ) {
						elem.value = val;
					}
					return value;
				}
			}
		}
	}
});

// Hook for boolean attributes
boolHook = {
	set: function( elem, value, name ) {
		if ( value === false ) {
			// Remove boolean attributes when set to false
			jQuery.removeAttr( elem, name );
		} else if ( getSetInput && getSetAttribute || !ruseDefault.test( name ) ) {
			// IE<8 needs the *property* name
			elem.setAttribute( !getSetAttribute && jQuery.propFix[ name ] || name, name );

		// Use defaultChecked and defaultSelected for oldIE
		} else {
			elem[ jQuery.camelCase( "default-" + name ) ] = elem[ name ] = true;
		}

		return name;
	}
};

// Retrieve booleans specially
jQuery.each( jQuery.expr.match.bool.source.match( /\w+/g ), function( i, name ) {

	var getter = attrHandle[ name ] || jQuery.find.attr;

	attrHandle[ name ] = getSetInput && getSetAttribute || !ruseDefault.test( name ) ?
		function( elem, name, isXML ) {
			var ret, handle;
			if ( !isXML ) {
				// Avoid an infinite loop by temporarily removing this function from the getter
				handle = attrHandle[ name ];
				attrHandle[ name ] = ret;
				ret = getter( elem, name, isXML ) != null ?
					name.toLowerCase() :
					null;
				attrHandle[ name ] = handle;
			}
			return ret;
		} :
		function( elem, name, isXML ) {
			if ( !isXML ) {
				return elem[ jQuery.camelCase( "default-" + name ) ] ?
					name.toLowerCase() :
					null;
			}
		};
});

// fix oldIE attroperties
if ( !getSetInput || !getSetAttribute ) {
	jQuery.attrHooks.value = {
		set: function( elem, value, name ) {
			if ( jQuery.nodeName( elem, "input" ) ) {
				// Does not return so that setAttribute is also used
				elem.defaultValue = value;
			} else {
				// Use nodeHook if defined (#1954); otherwise setAttribute is fine
				return nodeHook && nodeHook.set( elem, value, name );
			}
		}
	};
}

// IE6/7 do not support getting/setting some attributes with get/setAttribute
if ( !getSetAttribute ) {

	// Use this for any attribute in IE6/7
	// This fixes almost every IE6/7 issue
	nodeHook = {
		set: function( elem, value, name ) {
			// Set the existing or create a new attribute node
			var ret = elem.getAttributeNode( name );
			if ( !ret ) {
				elem.setAttributeNode(
					(ret = elem.ownerDocument.createAttribute( name ))
				);
			}

			ret.value = value += "";

			// Break association with cloned elements by also using setAttribute (#9646)
			if ( name === "value" || value === elem.getAttribute( name ) ) {
				return value;
			}
		}
	};

	// Some attributes are constructed with empty-string values when not defined
	attrHandle.id = attrHandle.name = attrHandle.coords =
		function( elem, name, isXML ) {
			var ret;
			if ( !isXML ) {
				return (ret = elem.getAttributeNode( name )) && ret.value !== "" ?
					ret.value :
					null;
			}
		};

	// Fixing value retrieval on a button requires this module
	jQuery.valHooks.button = {
		get: function( elem, name ) {
			var ret = elem.getAttributeNode( name );
			if ( ret && ret.specified ) {
				return ret.value;
			}
		},
		set: nodeHook.set
	};

	// Set contenteditable to false on removals(#10429)
	// Setting to empty string throws an error as an invalid value
	jQuery.attrHooks.contenteditable = {
		set: function( elem, value, name ) {
			nodeHook.set( elem, value === "" ? false : value, name );
		}
	};

	// Set width and height to auto instead of 0 on empty string( Bug #8150 )
	// This is for removals
	jQuery.each([ "width", "height" ], function( i, name ) {
		jQuery.attrHooks[ name ] = {
			set: function( elem, value ) {
				if ( value === "" ) {
					elem.setAttribute( name, "auto" );
					return value;
				}
			}
		};
	});
}

if ( !support.style ) {
	jQuery.attrHooks.style = {
		get: function( elem ) {
			// Return undefined in the case of empty string
			// Note: IE uppercases css property names, but if we were to .toLowerCase()
			// .cssText, that would destroy case senstitivity in URL's, like in "background"
			return elem.style.cssText || undefined;
		},
		set: function( elem, value ) {
			return ( elem.style.cssText = value + "" );
		}
	};
}




var rfocusable = /^(?:input|select|textarea|button|object)$/i,
	rclickable = /^(?:a|area)$/i;

jQuery.fn.extend({
	prop: function( name, value ) {
		return access( this, jQuery.prop, name, value, arguments.length > 1 );
	},

	removeProp: function( name ) {
		name = jQuery.propFix[ name ] || name;
		return this.each(function() {
			// try/catch handles cases where IE balks (such as removing a property on window)
			try {
				this[ name ] = undefined;
				delete this[ name ];
			} catch( e ) {}
		});
	}
});

jQuery.extend({
	propFix: {
		"for": "htmlFor",
		"class": "className"
	},

	prop: function( elem, name, value ) {
		var ret, hooks, notxml,
			nType = elem.nodeType;

		// don't get/set properties on text, comment and attribute nodes
		if ( !elem || nType === 3 || nType === 8 || nType === 2 ) {
			return;
		}

		notxml = nType !== 1 || !jQuery.isXMLDoc( elem );

		if ( notxml ) {
			// Fix name and attach hooks
			name = jQuery.propFix[ name ] || name;
			hooks = jQuery.propHooks[ name ];
		}

		if ( value !== undefined ) {
			return hooks && "set" in hooks && (ret = hooks.set( elem, value, name )) !== undefined ?
				ret :
				( elem[ name ] = value );

		} else {
			return hooks && "get" in hooks && (ret = hooks.get( elem, name )) !== null ?
				ret :
				elem[ name ];
		}
	},

	propHooks: {
		tabIndex: {
			get: function( elem ) {
				// elem.tabIndex doesn't always return the correct value when it hasn't been explicitly set
				// http://fluidproject.org/blog/2008/01/09/getting-setting-and-removing-tabindex-values-with-javascript/
				// Use proper attribute retrieval(#12072)
				var tabindex = jQuery.find.attr( elem, "tabindex" );

				return tabindex ?
					parseInt( tabindex, 10 ) :
					rfocusable.test( elem.nodeName ) || rclickable.test( elem.nodeName ) && elem.href ?
						0 :
						-1;
			}
		}
	}
});

// Some attributes require a special call on IE
// http://msdn.microsoft.com/en-us/library/ms536429%28VS.85%29.aspx
if ( !support.hrefNormalized ) {
	// href/src property should get the full normalized URL (#10299/#12915)
	jQuery.each([ "href", "src" ], function( i, name ) {
		jQuery.propHooks[ name ] = {
			get: function( elem ) {
				return elem.getAttribute( name, 4 );
			}
		};
	});
}

// Support: Safari, IE9+
// mis-reports the default selected property of an option
// Accessing the parent's selectedIndex property fixes it
if ( !support.optSelected ) {
	jQuery.propHooks.selected = {
		get: function( elem ) {
			var parent = elem.parentNode;

			if ( parent ) {
				parent.selectedIndex;

				// Make sure that it also works with optgroups, see #5701
				if ( parent.parentNode ) {
					parent.parentNode.selectedIndex;
				}
			}
			return null;
		}
	};
}

jQuery.each([
	"tabIndex",
	"readOnly",
	"maxLength",
	"cellSpacing",
	"cellPadding",
	"rowSpan",
	"colSpan",
	"useMap",
	"frameBorder",
	"contentEditable"
], function() {
	jQuery.propFix[ this.toLowerCase() ] = this;
});

// IE6/7 call enctype encoding
if ( !support.enctype ) {
	jQuery.propFix.enctype = "encoding";
}




var rclass = /[\t\r\n\f]/g;

jQuery.fn.extend({
	addClass: function( value ) {
		var classes, elem, cur, clazz, j, finalValue,
			i = 0,
			len = this.length,
			proceed = typeof value === "string" && value;

		if ( jQuery.isFunction( value ) ) {
			return this.each(function( j ) {
				jQuery( this ).addClass( value.call( this, j, this.className ) );
			});
		}

		if ( proceed ) {
			// The disjunction here is for better compressibility (see removeClass)
			classes = ( value || "" ).match( rnotwhite ) || [];

			for ( ; i < len; i++ ) {
				elem = this[ i ];
				cur = elem.nodeType === 1 && ( elem.className ?
					( " " + elem.className + " " ).replace( rclass, " " ) :
					" "
				);

				if ( cur ) {
					j = 0;
					while ( (clazz = classes[j++]) ) {
						if ( cur.indexOf( " " + clazz + " " ) < 0 ) {
							cur += clazz + " ";
						}
					}

					// only assign if different to avoid unneeded rendering.
					finalValue = jQuery.trim( cur );
					if ( elem.className !== finalValue ) {
						elem.className = finalValue;
					}
				}
			}
		}

		return this;
	},

	removeClass: function( value ) {
		var classes, elem, cur, clazz, j, finalValue,
			i = 0,
			len = this.length,
			proceed = arguments.length === 0 || typeof value === "string" && value;

		if ( jQuery.isFunction( value ) ) {
			return this.each(function( j ) {
				jQuery( this ).removeClass( value.call( this, j, this.className ) );
			});
		}
		if ( proceed ) {
			classes = ( value || "" ).match( rnotwhite ) || [];

			for ( ; i < len; i++ ) {
				elem = this[ i ];
				// This expression is here for better compressibility (see addClass)
				cur = elem.nodeType === 1 && ( elem.className ?
					( " " + elem.className + " " ).replace( rclass, " " ) :
					""
				);

				if ( cur ) {
					j = 0;
					while ( (clazz = classes[j++]) ) {
						// Remove *all* instances
						while ( cur.indexOf( " " + clazz + " " ) >= 0 ) {
							cur = cur.replace( " " + clazz + " ", " " );
						}
					}

					// only assign if different to avoid unneeded rendering.
					finalValue = value ? jQuery.trim( cur ) : "";
					if ( elem.className !== finalValue ) {
						elem.className = finalValue;
					}
				}
			}
		}

		return this;
	},

	toggleClass: function( value, stateVal ) {
		var type = typeof value;

		if ( typeof stateVal === "boolean" && type === "string" ) {
			return stateVal ? this.addClass( value ) : this.removeClass( value );
		}

		if ( jQuery.isFunction( value ) ) {
			return this.each(function( i ) {
				jQuery( this ).toggleClass( value.call(this, i, this.className, stateVal), stateVal );
			});
		}

		return this.each(function() {
			if ( type === "string" ) {
				// toggle individual class names
				var className,
					i = 0,
					self = jQuery( this ),
					classNames = value.match( rnotwhite ) || [];

				while ( (className = classNames[ i++ ]) ) {
					// check each className given, space separated list
					if ( self.hasClass( className ) ) {
						self.removeClass( className );
					} else {
						self.addClass( className );
					}
				}

			// Toggle whole class name
			} else if ( type === strundefined || type === "boolean" ) {
				if ( this.className ) {
					// store className if set
					jQuery._data( this, "__className__", this.className );
				}

				// If the element has a class name or if we're passed "false",
				// then remove the whole classname (if there was one, the above saved it).
				// Otherwise bring back whatever was previously saved (if anything),
				// falling back to the empty string if nothing was stored.
				this.className = this.className || value === false ? "" : jQuery._data( this, "__className__" ) || "";
			}
		});
	},

	hasClass: function( selector ) {
		var className = " " + selector + " ",
			i = 0,
			l = this.length;
		for ( ; i < l; i++ ) {
			if ( this[i].nodeType === 1 && (" " + this[i].className + " ").replace(rclass, " ").indexOf( className ) >= 0 ) {
				return true;
			}
		}

		return false;
	}
});




// Return jQuery for attributes-only inclusion


jQuery.each( ("blur focus focusin focusout load resize scroll unload click dblclick " +
	"mousedown mouseup mousemove mouseover mouseout mouseenter mouseleave " +
	"change select submit keydown keypress keyup error contextmenu").split(" "), function( i, name ) {

	// Handle event binding
	jQuery.fn[ name ] = function( data, fn ) {
		return arguments.length > 0 ?
			this.on( name, null, data, fn ) :
			this.trigger( name );
	};
});

jQuery.fn.extend({
	hover: function( fnOver, fnOut ) {
		return this.mouseenter( fnOver ).mouseleave( fnOut || fnOver );
	},

	bind: function( types, data, fn ) {
		return this.on( types, null, data, fn );
	},
	unbind: function( types, fn ) {
		return this.off( types, null, fn );
	},

	delegate: function( selector, types, data, fn ) {
		return this.on( types, selector, data, fn );
	},
	undelegate: function( selector, types, fn ) {
		// ( namespace ) or ( selector, types [, fn] )
		return arguments.length === 1 ? this.off( selector, "**" ) : this.off( types, selector || "**", fn );
	}
});


var nonce = jQuery.now();

var rquery = (/\?/);



var rvalidtokens = /(,)|(\[|{)|(}|])|"(?:[^"\\\r\n]|\\["\\\/bfnrt]|\\u[\da-fA-F]{4})*"\s*:?|true|false|null|-?(?!0\d)\d+(?:\.\d+|)(?:[eE][+-]?\d+|)/g;

jQuery.parseJSON = function( data ) {
	// Attempt to parse using the native JSON parser first
	if ( window.JSON && window.JSON.parse ) {
		// Support: Android 2.3
		// Workaround failure to string-cast null input
		return window.JSON.parse( data + "" );
	}

	var requireNonComma,
		depth = null,
		str = jQuery.trim( data + "" );

	// Guard against invalid (and possibly dangerous) input by ensuring that nothing remains
	// after removing valid tokens
	return str && !jQuery.trim( str.replace( rvalidtokens, function( token, comma, open, close ) {

		// Force termination if we see a misplaced comma
		if ( requireNonComma && comma ) {
			depth = 0;
		}

		// Perform no more replacements after returning to outermost depth
		if ( depth === 0 ) {
			return token;
		}

		// Commas must not follow "[", "{", or ","
		requireNonComma = open || comma;

		// Determine new depth
		// array/object open ("[" or "{"): depth += true - false (increment)
		// array/object close ("]" or "}"): depth += false - true (decrement)
		// other cases ("," or primitive): depth += true - true (numeric cast)
		depth += !close - !open;

		// Remove this token
		return "";
	}) ) ?
		( Function( "return " + str ) )() :
		jQuery.error( "Invalid JSON: " + data );
};


// Cross-browser xml parsing
jQuery.parseXML = function( data ) {
	var xml, tmp;
	if ( !data || typeof data !== "string" ) {
		return null;
	}
	try {
		if ( window.DOMParser ) { // Standard
			tmp = new DOMParser();
			xml = tmp.parseFromString( data, "text/xml" );
		} else { // IE
			xml = new ActiveXObject( "Microsoft.XMLDOM" );
			xml.async = "false";
			xml.loadXML( data );
		}
	} catch( e ) {
		xml = undefined;
	}
	if ( !xml || !xml.documentElement || xml.getElementsByTagName( "parsererror" ).length ) {
		jQuery.error( "Invalid XML: " + data );
	}
	return xml;
};


var
	// Document location
	ajaxLocParts,
	ajaxLocation,

	rhash = /#.*$/,
	rts = /([?&])_=[^&]*/,
	rheaders = /^(.*?):[ \t]*([^\r\n]*)\r?$/mg, // IE leaves an \r character at EOL
	// #7653, #8125, #8152: local protocol detection
	rlocalProtocol = /^(?:about|app|app-storage|.+-extension|file|res|widget):$/,
	rnoContent = /^(?:GET|HEAD)$/,
	rprotocol = /^\/\//,
	rurl = /^([\w.+-]+:)(?:\/\/(?:[^\/?#]*@|)([^\/?#:]*)(?::(\d+)|)|)/,

	/* Prefilters
	 * 1) They are useful to introduce custom dataTypes (see ajax/jsonp.js for an example)
	 * 2) These are called:
	 *    - BEFORE asking for a transport
	 *    - AFTER param serialization (s.data is a string if s.processData is true)
	 * 3) key is the dataType
	 * 4) the catchall symbol "*" can be used
	 * 5) execution will start with transport dataType and THEN continue down to "*" if needed
	 */
	prefilters = {},

	/* Transports bindings
	 * 1) key is the dataType
	 * 2) the catchall symbol "*" can be used
	 * 3) selection will start with transport dataType and THEN go to "*" if needed
	 */
	transports = {},

	// Avoid comment-prolog char sequence (#10098); must appease lint and evade compression
	allTypes = "*/".concat("*");

// #8138, IE may throw an exception when accessing
// a field from window.location if document.domain has been set
try {
	ajaxLocation = location.href;
} catch( e ) {
	// Use the href attribute of an A element
	// since IE will modify it given document.location
	ajaxLocation = document.createElement( "a" );
	ajaxLocation.href = "";
	ajaxLocation = ajaxLocation.href;
}

// Segment location into parts
ajaxLocParts = rurl.exec( ajaxLocation.toLowerCase() ) || [];

// Base "constructor" for jQuery.ajaxPrefilter and jQuery.ajaxTransport
function addToPrefiltersOrTransports( structure ) {

	// dataTypeExpression is optional and defaults to "*"
	return function( dataTypeExpression, func ) {

		if ( typeof dataTypeExpression !== "string" ) {
			func = dataTypeExpression;
			dataTypeExpression = "*";
		}

		var dataType,
			i = 0,
			dataTypes = dataTypeExpression.toLowerCase().match( rnotwhite ) || [];

		if ( jQuery.isFunction( func ) ) {
			// For each dataType in the dataTypeExpression
			while ( (dataType = dataTypes[i++]) ) {
				// Prepend if requested
				if ( dataType.charAt( 0 ) === "+" ) {
					dataType = dataType.slice( 1 ) || "*";
					(structure[ dataType ] = structure[ dataType ] || []).unshift( func );

				// Otherwise append
				} else {
					(structure[ dataType ] = structure[ dataType ] || []).push( func );
				}
			}
		}
	};
}

// Base inspection function for prefilters and transports
function inspectPrefiltersOrTransports( structure, options, originalOptions, jqXHR ) {

	var inspected = {},
		seekingTransport = ( structure === transports );

	function inspect( dataType ) {
		var selected;
		inspected[ dataType ] = true;
		jQuery.each( structure[ dataType ] || [], function( _, prefilterOrFactory ) {
			var dataTypeOrTransport = prefilterOrFactory( options, originalOptions, jqXHR );
			if ( typeof dataTypeOrTransport === "string" && !seekingTransport && !inspected[ dataTypeOrTransport ] ) {
				options.dataTypes.unshift( dataTypeOrTransport );
				inspect( dataTypeOrTransport );
				return false;
			} else if ( seekingTransport ) {
				return !( selected = dataTypeOrTransport );
			}
		});
		return selected;
	}

	return inspect( options.dataTypes[ 0 ] ) || !inspected[ "*" ] && inspect( "*" );
}

// A special extend for ajax options
// that takes "flat" options (not to be deep extended)
// Fixes #9887
function ajaxExtend( target, src ) {
	var deep, key,
		flatOptions = jQuery.ajaxSettings.flatOptions || {};

	for ( key in src ) {
		if ( src[ key ] !== undefined ) {
			( flatOptions[ key ] ? target : ( deep || (deep = {}) ) )[ key ] = src[ key ];
		}
	}
	if ( deep ) {
		jQuery.extend( true, target, deep );
	}

	return target;
}

/* Handles responses to an ajax request:
 * - finds the right dataType (mediates between content-type and expected dataType)
 * - returns the corresponding response
 */
function ajaxHandleResponses( s, jqXHR, responses ) {
	var firstDataType, ct, finalDataType, type,
		contents = s.contents,
		dataTypes = s.dataTypes;

	// Remove auto dataType and get content-type in the process
	while ( dataTypes[ 0 ] === "*" ) {
		dataTypes.shift();
		if ( ct === undefined ) {
			ct = s.mimeType || jqXHR.getResponseHeader("Content-Type");
		}
	}

	// Check if we're dealing with a known content-type
	if ( ct ) {
		for ( type in contents ) {
			if ( contents[ type ] && contents[ type ].test( ct ) ) {
				dataTypes.unshift( type );
				break;
			}
		}
	}

	// Check to see if we have a response for the expected dataType
	if ( dataTypes[ 0 ] in responses ) {
		finalDataType = dataTypes[ 0 ];
	} else {
		// Try convertible dataTypes
		for ( type in responses ) {
			if ( !dataTypes[ 0 ] || s.converters[ type + " " + dataTypes[0] ] ) {
				finalDataType = type;
				break;
			}
			if ( !firstDataType ) {
				firstDataType = type;
			}
		}
		// Or just use first one
		finalDataType = finalDataType || firstDataType;
	}

	// If we found a dataType
	// We add the dataType to the list if needed
	// and return the corresponding response
	if ( finalDataType ) {
		if ( finalDataType !== dataTypes[ 0 ] ) {
			dataTypes.unshift( finalDataType );
		}
		return responses[ finalDataType ];
	}
}

/* Chain conversions given the request and the original response
 * Also sets the responseXXX fields on the jqXHR instance
 */
function ajaxConvert( s, response, jqXHR, isSuccess ) {
	var conv2, current, conv, tmp, prev,
		converters = {},
		// Work with a copy of dataTypes in case we need to modify it for conversion
		dataTypes = s.dataTypes.slice();

	// Create converters map with lowercased keys
	if ( dataTypes[ 1 ] ) {
		for ( conv in s.converters ) {
			converters[ conv.toLowerCase() ] = s.converters[ conv ];
		}
	}

	current = dataTypes.shift();

	// Convert to each sequential dataType
	while ( current ) {

		if ( s.responseFields[ current ] ) {
			jqXHR[ s.responseFields[ current ] ] = response;
		}

		// Apply the dataFilter if provided
		if ( !prev && isSuccess && s.dataFilter ) {
			response = s.dataFilter( response, s.dataType );
		}

		prev = current;
		current = dataTypes.shift();

		if ( current ) {

			// There's only work to do if current dataType is non-auto
			if ( current === "*" ) {

				current = prev;

			// Convert response if prev dataType is non-auto and differs from current
			} else if ( prev !== "*" && prev !== current ) {

				// Seek a direct converter
				conv = converters[ prev + " " + current ] || converters[ "* " + current ];

				// If none found, seek a pair
				if ( !conv ) {
					for ( conv2 in converters ) {

						// If conv2 outputs current
						tmp = conv2.split( " " );
						if ( tmp[ 1 ] === current ) {

							// If prev can be converted to accepted input
							conv = converters[ prev + " " + tmp[ 0 ] ] ||
								converters[ "* " + tmp[ 0 ] ];
							if ( conv ) {
								// Condense equivalence converters
								if ( conv === true ) {
									conv = converters[ conv2 ];

								// Otherwise, insert the intermediate dataType
								} else if ( converters[ conv2 ] !== true ) {
									current = tmp[ 0 ];
									dataTypes.unshift( tmp[ 1 ] );
								}
								break;
							}
						}
					}
				}

				// Apply converter (if not an equivalence)
				if ( conv !== true ) {

					// Unless errors are allowed to bubble, catch and return them
					if ( conv && s[ "throws" ] ) {
						response = conv( response );
					} else {
						try {
							response = conv( response );
						} catch ( e ) {
							return { state: "parsererror", error: conv ? e : "No conversion from " + prev + " to " + current };
						}
					}
				}
			}
		}
	}

	return { state: "success", data: response };
}

jQuery.extend({

	// Counter for holding the number of active queries
	active: 0,

	// Last-Modified header cache for next request
	lastModified: {},
	etag: {},

	ajaxSettings: {
		url: ajaxLocation,
		type: "GET",
		isLocal: rlocalProtocol.test( ajaxLocParts[ 1 ] ),
		global: true,
		processData: true,
		async: true,
		contentType: "application/x-www-form-urlencoded; charset=UTF-8",
		/*
		timeout: 0,
		data: null,
		dataType: null,
		username: null,
		password: null,
		cache: null,
		throws: false,
		traditional: false,
		headers: {},
		*/

		accepts: {
			"*": allTypes,
			text: "text/plain",
			html: "text/html",
			xml: "application/xml, text/xml",
			json: "application/json, text/javascript"
		},

		contents: {
			xml: /xml/,
			html: /html/,
			json: /json/
		},

		responseFields: {
			xml: "responseXML",
			text: "responseText",
			json: "responseJSON"
		},

		// Data converters
		// Keys separate source (or catchall "*") and destination types with a single space
		converters: {

			// Convert anything to text
			"* text": String,

			// Text to html (true = no transformation)
			"text html": true,

			// Evaluate text as a json expression
			"text json": jQuery.parseJSON,

			// Parse text as xml
			"text xml": jQuery.parseXML
		},

		// For options that shouldn't be deep extended:
		// you can add your own custom options here if
		// and when you create one that shouldn't be
		// deep extended (see ajaxExtend)
		flatOptions: {
			url: true,
			context: true
		}
	},

	// Creates a full fledged settings object into target
	// with both ajaxSettings and settings fields.
	// If target is omitted, writes into ajaxSettings.
	ajaxSetup: function( target, settings ) {
		return settings ?

			// Building a settings object
			ajaxExtend( ajaxExtend( target, jQuery.ajaxSettings ), settings ) :

			// Extending ajaxSettings
			ajaxExtend( jQuery.ajaxSettings, target );
	},

	ajaxPrefilter: addToPrefiltersOrTransports( prefilters ),
	ajaxTransport: addToPrefiltersOrTransports( transports ),

	// Main method
	ajax: function( url, options ) {

		// If url is an object, simulate pre-1.5 signature
		if ( typeof url === "object" ) {
			options = url;
			url = undefined;
		}

		// Force options to be an object
		options = options || {};

		var // Cross-domain detection vars
			parts,
			// Loop variable
			i,
			// URL without anti-cache param
			cacheURL,
			// Response headers as string
			responseHeadersString,
			// timeout handle
			timeoutTimer,

			// To know if global events are to be dispatched
			fireGlobals,

			transport,
			// Response headers
			responseHeaders,
			// Create the final options object
			s = jQuery.ajaxSetup( {}, options ),
			// Callbacks context
			callbackContext = s.context || s,
			// Context for global events is callbackContext if it is a DOM node or jQuery collection
			globalEventContext = s.context && ( callbackContext.nodeType || callbackContext.jquery ) ?
				jQuery( callbackContext ) :
				jQuery.event,
			// Deferreds
			deferred = jQuery.Deferred(),
			completeDeferred = jQuery.Callbacks("once memory"),
			// Status-dependent callbacks
			statusCode = s.statusCode || {},
			// Headers (they are sent all at once)
			requestHeaders = {},
			requestHeadersNames = {},
			// The jqXHR state
			state = 0,
			// Default abort message
			strAbort = "canceled",
			// Fake xhr
			jqXHR = {
				readyState: 0,

				// Builds headers hashtable if needed
				getResponseHeader: function( key ) {
					var match;
					if ( state === 2 ) {
						if ( !responseHeaders ) {
							responseHeaders = {};
							while ( (match = rheaders.exec( responseHeadersString )) ) {
								responseHeaders[ match[1].toLowerCase() ] = match[ 2 ];
							}
						}
						match = responseHeaders[ key.toLowerCase() ];
					}
					return match == null ? null : match;
				},

				// Raw string
				getAllResponseHeaders: function() {
					return state === 2 ? responseHeadersString : null;
				},

				// Caches the header
				setRequestHeader: function( name, value ) {
					var lname = name.toLowerCase();
					if ( !state ) {
						name = requestHeadersNames[ lname ] = requestHeadersNames[ lname ] || name;
						requestHeaders[ name ] = value;
					}
					return this;
				},

				// Overrides response content-type header
				overrideMimeType: function( type ) {
					if ( !state ) {
						s.mimeType = type;
					}
					return this;
				},

				// Status-dependent callbacks
				statusCode: function( map ) {
					var code;
					if ( map ) {
						if ( state < 2 ) {
							for ( code in map ) {
								// Lazy-add the new callback in a way that preserves old ones
								statusCode[ code ] = [ statusCode[ code ], map[ code ] ];
							}
						} else {
							// Execute the appropriate callbacks
							jqXHR.always( map[ jqXHR.status ] );
						}
					}
					return this;
				},

				// Cancel the request
				abort: function( statusText ) {
					var finalText = statusText || strAbort;
					if ( transport ) {
						transport.abort( finalText );
					}
					done( 0, finalText );
					return this;
				}
			};

		// Attach deferreds
		deferred.promise( jqXHR ).complete = completeDeferred.add;
		jqXHR.success = jqXHR.done;
		jqXHR.error = jqXHR.fail;

		// Remove hash character (#7531: and string promotion)
		// Add protocol if not provided (#5866: IE7 issue with protocol-less urls)
		// Handle falsy url in the settings object (#10093: consistency with old signature)
		// We also use the url parameter if available
		s.url = ( ( url || s.url || ajaxLocation ) + "" ).replace( rhash, "" ).replace( rprotocol, ajaxLocParts[ 1 ] + "//" );

		// Alias method option to type as per ticket #12004
		s.type = options.method || options.type || s.method || s.type;

		// Extract dataTypes list
		s.dataTypes = jQuery.trim( s.dataType || "*" ).toLowerCase().match( rnotwhite ) || [ "" ];

		// A cross-domain request is in order when we have a protocol:host:port mismatch
		if ( s.crossDomain == null ) {
			parts = rurl.exec( s.url.toLowerCase() );
			s.crossDomain = !!( parts &&
				( parts[ 1 ] !== ajaxLocParts[ 1 ] || parts[ 2 ] !== ajaxLocParts[ 2 ] ||
					( parts[ 3 ] || ( parts[ 1 ] === "http:" ? "80" : "443" ) ) !==
						( ajaxLocParts[ 3 ] || ( ajaxLocParts[ 1 ] === "http:" ? "80" : "443" ) ) )
			);
		}

		// Convert data if not already a string
		if ( s.data && s.processData && typeof s.data !== "string" ) {
			s.data = jQuery.param( s.data, s.traditional );
		}

		// Apply prefilters
		inspectPrefiltersOrTransports( prefilters, s, options, jqXHR );

		// If request was aborted inside a prefilter, stop there
		if ( state === 2 ) {
			return jqXHR;
		}

		// We can fire global events as of now if asked to
		fireGlobals = s.global;

		// Watch for a new set of requests
		if ( fireGlobals && jQuery.active++ === 0 ) {
			jQuery.event.trigger("ajaxStart");
		}

		// Uppercase the type
		s.type = s.type.toUpperCase();

		// Determine if request has content
		s.hasContent = !rnoContent.test( s.type );

		// Save the URL in case we're toying with the If-Modified-Since
		// and/or If-None-Match header later on
		cacheURL = s.url;

		// More options handling for requests with no content
		if ( !s.hasContent ) {

			// If data is available, append data to url
			if ( s.data ) {
				cacheURL = ( s.url += ( rquery.test( cacheURL ) ? "&" : "?" ) + s.data );
				// #9682: remove data so that it's not used in an eventual retry
				delete s.data;
			}

			// Add anti-cache in url if needed
			if ( s.cache === false ) {
				s.url = rts.test( cacheURL ) ?

					// If there is already a '_' parameter, set its value
					cacheURL.replace( rts, "$1_=" + nonce++ ) :

					// Otherwise add one to the end
					cacheURL + ( rquery.test( cacheURL ) ? "&" : "?" ) + "_=" + nonce++;
			}
		}

		// Set the If-Modified-Since and/or If-None-Match header, if in ifModified mode.
		if ( s.ifModified ) {
			if ( jQuery.lastModified[ cacheURL ] ) {
				jqXHR.setRequestHeader( "If-Modified-Since", jQuery.lastModified[ cacheURL ] );
			}
			if ( jQuery.etag[ cacheURL ] ) {
				jqXHR.setRequestHeader( "If-None-Match", jQuery.etag[ cacheURL ] );
			}
		}

		// Set the correct header, if data is being sent
		if ( s.data && s.hasContent && s.contentType !== false || options.contentType ) {
			jqXHR.setRequestHeader( "Content-Type", s.contentType );
		}

		// Set the Accepts header for the server, depending on the dataType
		jqXHR.setRequestHeader(
			"Accept",
			s.dataTypes[ 0 ] && s.accepts[ s.dataTypes[0] ] ?
				s.accepts[ s.dataTypes[0] ] + ( s.dataTypes[ 0 ] !== "*" ? ", " + allTypes + "; q=0.01" : "" ) :
				s.accepts[ "*" ]
		);

		// Check for headers option
		for ( i in s.headers ) {
			jqXHR.setRequestHeader( i, s.headers[ i ] );
		}

		// Allow custom headers/mimetypes and early abort
		if ( s.beforeSend && ( s.beforeSend.call( callbackContext, jqXHR, s ) === false || state === 2 ) ) {
			// Abort if not done already and return
			return jqXHR.abort();
		}

		// aborting is no longer a cancellation
		strAbort = "abort";

		// Install callbacks on deferreds
		for ( i in { success: 1, error: 1, complete: 1 } ) {
			jqXHR[ i ]( s[ i ] );
		}

		// Get transport
		transport = inspectPrefiltersOrTransports( transports, s, options, jqXHR );

		// If no transport, we auto-abort
		if ( !transport ) {
			done( -1, "No Transport" );
		} else {
			jqXHR.readyState = 1;

			// Send global event
			if ( fireGlobals ) {
				globalEventContext.trigger( "ajaxSend", [ jqXHR, s ] );
			}
			// Timeout
			if ( s.async && s.timeout > 0 ) {
				timeoutTimer = setTimeout(function() {
					jqXHR.abort("timeout");
				}, s.timeout );
			}

			try {
				state = 1;
				transport.send( requestHeaders, done );
			} catch ( e ) {
				// Propagate exception as error if not done
				if ( state < 2 ) {
					done( -1, e );
				// Simply rethrow otherwise
				} else {
					throw e;
				}
			}
		}

		// Callback for when everything is done
		function done( status, nativeStatusText, responses, headers ) {
			var isSuccess, success, error, response, modified,
				statusText = nativeStatusText;

			// Called once
			if ( state === 2 ) {
				return;
			}

			// State is "done" now
			state = 2;

			// Clear timeout if it exists
			if ( timeoutTimer ) {
				clearTimeout( timeoutTimer );
			}

			// Dereference transport for early garbage collection
			// (no matter how long the jqXHR object will be used)
			transport = undefined;

			// Cache response headers
			responseHeadersString = headers || "";

			// Set readyState
			jqXHR.readyState = status > 0 ? 4 : 0;

			// Determine if successful
			isSuccess = status >= 200 && status < 300 || status === 304;

			// Get response data
			if ( responses ) {
				response = ajaxHandleResponses( s, jqXHR, responses );
			}

			// Convert no matter what (that way responseXXX fields are always set)
			response = ajaxConvert( s, response, jqXHR, isSuccess );

			// If successful, handle type chaining
			if ( isSuccess ) {

				// Set the If-Modified-Since and/or If-None-Match header, if in ifModified mode.
				if ( s.ifModified ) {
					modified = jqXHR.getResponseHeader("Last-Modified");
					if ( modified ) {
						jQuery.lastModified[ cacheURL ] = modified;
					}
					modified = jqXHR.getResponseHeader("etag");
					if ( modified ) {
						jQuery.etag[ cacheURL ] = modified;
					}
				}

				// if no content
				if ( status === 204 || s.type === "HEAD" ) {
					statusText = "nocontent";

				// if not modified
				} else if ( status === 304 ) {
					statusText = "notmodified";

				// If we have data, let's convert it
				} else {
					statusText = response.state;
					success = response.data;
					error = response.error;
					isSuccess = !error;
				}
			} else {
				// We extract error from statusText
				// then normalize statusText and status for non-aborts
				error = statusText;
				if ( status || !statusText ) {
					statusText = "error";
					if ( status < 0 ) {
						status = 0;
					}
				}
			}

			// Set data for the fake xhr object
			jqXHR.status = status;
			jqXHR.statusText = ( nativeStatusText || statusText ) + "";

			// Success/Error
			if ( isSuccess ) {
				deferred.resolveWith( callbackContext, [ success, statusText, jqXHR ] );
			} else {
				deferred.rejectWith( callbackContext, [ jqXHR, statusText, error ] );
			}

			// Status-dependent callbacks
			jqXHR.statusCode( statusCode );
			statusCode = undefined;

			if ( fireGlobals ) {
				globalEventContext.trigger( isSuccess ? "ajaxSuccess" : "ajaxError",
					[ jqXHR, s, isSuccess ? success : error ] );
			}

			// Complete
			completeDeferred.fireWith( callbackContext, [ jqXHR, statusText ] );

			if ( fireGlobals ) {
				globalEventContext.trigger( "ajaxComplete", [ jqXHR, s ] );
				// Handle the global AJAX counter
				if ( !( --jQuery.active ) ) {
					jQuery.event.trigger("ajaxStop");
				}
			}
		}

		return jqXHR;
	},

	getJSON: function( url, data, callback ) {
		return jQuery.get( url, data, callback, "json" );
	},

	getScript: function( url, callback ) {
		return jQuery.get( url, undefined, callback, "script" );
	}
});

jQuery.each( [ "get", "post" ], function( i, method ) {
	jQuery[ method ] = function( url, data, callback, type ) {
		// shift arguments if data argument was omitted
		if ( jQuery.isFunction( data ) ) {
			type = type || callback;
			callback = data;
			data = undefined;
		}

		return jQuery.ajax({
			url: url,
			type: method,
			dataType: type,
			data: data,
			success: callback
		});
	};
});

// Attach a bunch of functions for handling common AJAX events
jQuery.each( [ "ajaxStart", "ajaxStop", "ajaxComplete", "ajaxError", "ajaxSuccess", "ajaxSend" ], function( i, type ) {
	jQuery.fn[ type ] = function( fn ) {
		return this.on( type, fn );
	};
});


jQuery._evalUrl = function( url ) {
	return jQuery.ajax({
		url: url,
		type: "GET",
		dataType: "script",
		async: false,
		global: false,
		"throws": true
	});
};


jQuery.fn.extend({
	wrapAll: function( html ) {
		if ( jQuery.isFunction( html ) ) {
			return this.each(function(i) {
				jQuery(this).wrapAll( html.call(this, i) );
			});
		}

		if ( this[0] ) {
			// The elements to wrap the target around
			var wrap = jQuery( html, this[0].ownerDocument ).eq(0).clone(true);

			if ( this[0].parentNode ) {
				wrap.insertBefore( this[0] );
			}

			wrap.map(function() {
				var elem = this;

				while ( elem.firstChild && elem.firstChild.nodeType === 1 ) {
					elem = elem.firstChild;
				}

				return elem;
			}).append( this );
		}

		return this;
	},

	wrapInner: function( html ) {
		if ( jQuery.isFunction( html ) ) {
			return this.each(function(i) {
				jQuery(this).wrapInner( html.call(this, i) );
			});
		}

		return this.each(function() {
			var self = jQuery( this ),
				contents = self.contents();

			if ( contents.length ) {
				contents.wrapAll( html );

			} else {
				self.append( html );
			}
		});
	},

	wrap: function( html ) {
		var isFunction = jQuery.isFunction( html );

		return this.each(function(i) {
			jQuery( this ).wrapAll( isFunction ? html.call(this, i) : html );
		});
	},

	unwrap: function() {
		return this.parent().each(function() {
			if ( !jQuery.nodeName( this, "body" ) ) {
				jQuery( this ).replaceWith( this.childNodes );
			}
		}).end();
	}
});


jQuery.expr.filters.hidden = function( elem ) {
	// Support: Opera <= 12.12
	// Opera reports offsetWidths and offsetHeights less than zero on some elements
	return elem.offsetWidth <= 0 && elem.offsetHeight <= 0 ||
		(!support.reliableHiddenOffsets() &&
			((elem.style && elem.style.display) || jQuery.css( elem, "display" )) === "none");
};

jQuery.expr.filters.visible = function( elem ) {
	return !jQuery.expr.filters.hidden( elem );
};




var r20 = /%20/g,
	rbracket = /\[\]$/,
	rCRLF = /\r?\n/g,
	rsubmitterTypes = /^(?:submit|button|image|reset|file)$/i,
	rsubmittable = /^(?:input|select|textarea|keygen)/i;

function buildParams( prefix, obj, traditional, add ) {
	var name;

	if ( jQuery.isArray( obj ) ) {
		// Serialize array item.
		jQuery.each( obj, function( i, v ) {
			if ( traditional || rbracket.test( prefix ) ) {
				// Treat each array item as a scalar.
				add( prefix, v );

			} else {
				// Item is non-scalar (array or object), encode its numeric index.
				buildParams( prefix + "[" + ( typeof v === "object" ? i : "" ) + "]", v, traditional, add );
			}
		});

	} else if ( !traditional && jQuery.type( obj ) === "object" ) {
		// Serialize object item.
		for ( name in obj ) {
			buildParams( prefix + "[" + name + "]", obj[ name ], traditional, add );
		}

	} else {
		// Serialize scalar item.
		add( prefix, obj );
	}
}

// Serialize an array of form elements or a set of
// key/values into a query string
jQuery.param = function( a, traditional ) {
	var prefix,
		s = [],
		add = function( key, value ) {
			// If value is a function, invoke it and return its value
			value = jQuery.isFunction( value ) ? value() : ( value == null ? "" : value );
			s[ s.length ] = encodeURIComponent( key ) + "=" + encodeURIComponent( value );
		};

	// Set traditional to true for jQuery <= 1.3.2 behavior.
	if ( traditional === undefined ) {
		traditional = jQuery.ajaxSettings && jQuery.ajaxSettings.traditional;
	}

	// If an array was passed in, assume that it is an array of form elements.
	if ( jQuery.isArray( a ) || ( a.jquery && !jQuery.isPlainObject( a ) ) ) {
		// Serialize the form elements
		jQuery.each( a, function() {
			add( this.name, this.value );
		});

	} else {
		// If traditional, encode the "old" way (the way 1.3.2 or older
		// did it), otherwise encode params recursively.
		for ( prefix in a ) {
			buildParams( prefix, a[ prefix ], traditional, add );
		}
	}

	// Return the resulting serialization
	return s.join( "&" ).replace( r20, "+" );
};

jQuery.fn.extend({
	serialize: function() {
		return jQuery.param( this.serializeArray() );
	},
	serializeArray: function() {
		return this.map(function() {
			// Can add propHook for "elements" to filter or add form elements
			var elements = jQuery.prop( this, "elements" );
			return elements ? jQuery.makeArray( elements ) : this;
		})
		.filter(function() {
			var type = this.type;
			// Use .is(":disabled") so that fieldset[disabled] works
			return this.name && !jQuery( this ).is( ":disabled" ) &&
				rsubmittable.test( this.nodeName ) && !rsubmitterTypes.test( type ) &&
				( this.checked || !rcheckableType.test( type ) );
		})
		.map(function( i, elem ) {
			var val = jQuery( this ).val();

			return val == null ?
				null :
				jQuery.isArray( val ) ?
					jQuery.map( val, function( val ) {
						return { name: elem.name, value: val.replace( rCRLF, "\r\n" ) };
					}) :
					{ name: elem.name, value: val.replace( rCRLF, "\r\n" ) };
		}).get();
	}
});


// Create the request object
// (This is still attached to ajaxSettings for backward compatibility)
jQuery.ajaxSettings.xhr = window.ActiveXObject !== undefined ?
	// Support: IE6+
	function() {

		// XHR cannot access local files, always use ActiveX for that case
		return !this.isLocal &&

			// Support: IE7-8
			// oldIE XHR does not support non-RFC2616 methods (#13240)
			// See http://msdn.microsoft.com/en-us/library/ie/ms536648(v=vs.85).aspx
			// and http://www.w3.org/Protocols/rfc2616/rfc2616-sec9.html#sec9
			// Although this check for six methods instead of eight
			// since IE also does not support "trace" and "connect"
			/^(get|post|head|put|delete|options)$/i.test( this.type ) &&

			createStandardXHR() || createActiveXHR();
	} :
	// For all other browsers, use the standard XMLHttpRequest object
	createStandardXHR;

var xhrId = 0,
	xhrCallbacks = {},
	xhrSupported = jQuery.ajaxSettings.xhr();

// Support: IE<10
// Open requests must be manually aborted on unload (#5280)
if ( window.ActiveXObject ) {
	jQuery( window ).on( "unload", function() {
		for ( var key in xhrCallbacks ) {
			xhrCallbacks[ key ]( undefined, true );
		}
	});
}

// Determine support properties
support.cors = !!xhrSupported && ( "withCredentials" in xhrSupported );
xhrSupported = support.ajax = !!xhrSupported;

// Create transport if the browser can provide an xhr
if ( xhrSupported ) {

	jQuery.ajaxTransport(function( options ) {
		// Cross domain only allowed if supported through XMLHttpRequest
		if ( !options.crossDomain || support.cors ) {

			var callback;

			return {
				send: function( headers, complete ) {
					var i,
						xhr = options.xhr(),
						id = ++xhrId;

					// Open the socket
					xhr.open( options.type, options.url, options.async, options.username, options.password );

					// Apply custom fields if provided
					if ( options.xhrFields ) {
						for ( i in options.xhrFields ) {
							xhr[ i ] = options.xhrFields[ i ];
						}
					}

					// Override mime type if needed
					if ( options.mimeType && xhr.overrideMimeType ) {
						xhr.overrideMimeType( options.mimeType );
					}

					// X-Requested-With header
					// For cross-domain requests, seeing as conditions for a preflight are
					// akin to a jigsaw puzzle, we simply never set it to be sure.
					// (it can always be set on a per-request basis or even using ajaxSetup)
					// For same-domain requests, won't change header if already provided.
					if ( !options.crossDomain && !headers["X-Requested-With"] ) {
						headers["X-Requested-With"] = "XMLHttpRequest";
					}

					// Set headers
					for ( i in headers ) {
						// Support: IE<9
						// IE's ActiveXObject throws a 'Type Mismatch' exception when setting
						// request header to a null-value.
						//
						// To keep consistent with other XHR implementations, cast the value
						// to string and ignore `undefined`.
						if ( headers[ i ] !== undefined ) {
							xhr.setRequestHeader( i, headers[ i ] + "" );
						}
					}

					// Do send the request
					// This may raise an exception which is actually
					// handled in jQuery.ajax (so no try/catch here)
					xhr.send( ( options.hasContent && options.data ) || null );

					// Listener
					callback = function( _, isAbort ) {
						var status, statusText, responses;

						// Was never called and is aborted or complete
						if ( callback && ( isAbort || xhr.readyState === 4 ) ) {
							// Clean up
							delete xhrCallbacks[ id ];
							callback = undefined;
							xhr.onreadystatechange = jQuery.noop;

							// Abort manually if needed
							if ( isAbort ) {
								if ( xhr.readyState !== 4 ) {
									xhr.abort();
								}
							} else {
								responses = {};
								status = xhr.status;

								// Support: IE<10
								// Accessing binary-data responseText throws an exception
								// (#11426)
								if ( typeof xhr.responseText === "string" ) {
									responses.text = xhr.responseText;
								}

								// Firefox throws an exception when accessing
								// statusText for faulty cross-domain requests
								try {
									statusText = xhr.statusText;
								} catch( e ) {
									// We normalize with Webkit giving an empty statusText
									statusText = "";
								}

								// Filter status for non standard behaviors

								// If the request is local and we have data: assume a success
								// (success with no data won't get notified, that's the best we
								// can do given current implementations)
								if ( !status && options.isLocal && !options.crossDomain ) {
									status = responses.text ? 200 : 404;
								// IE - #1450: sometimes returns 1223 when it should be 204
								} else if ( status === 1223 ) {
									status = 204;
								}
							}
						}

						// Call complete if needed
						if ( responses ) {
							complete( status, statusText, responses, xhr.getAllResponseHeaders() );
						}
					};

					if ( !options.async ) {
						// if we're in sync mode we fire the callback
						callback();
					} else if ( xhr.readyState === 4 ) {
						// (IE6 & IE7) if it's in cache and has been
						// retrieved directly we need to fire the callback
						setTimeout( callback );
					} else {
						// Add to the list of active xhr callbacks
						xhr.onreadystatechange = xhrCallbacks[ id ] = callback;
					}
				},

				abort: function() {
					if ( callback ) {
						callback( undefined, true );
					}
				}
			};
		}
	});
}

// Functions to create xhrs
function createStandardXHR() {
	try {
		return new window.XMLHttpRequest();
	} catch( e ) {}
}

function createActiveXHR() {
	try {
		return new window.ActiveXObject( "Microsoft.XMLHTTP" );
	} catch( e ) {}
}




// Install script dataType
jQuery.ajaxSetup({
	accepts: {
		script: "text/javascript, application/javascript, application/ecmascript, application/x-ecmascript"
	},
	contents: {
		script: /(?:java|ecma)script/
	},
	converters: {
		"text script": function( text ) {
			jQuery.globalEval( text );
			return text;
		}
	}
});

// Handle cache's special case and global
jQuery.ajaxPrefilter( "script", function( s ) {
	if ( s.cache === undefined ) {
		s.cache = false;
	}
	if ( s.crossDomain ) {
		s.type = "GET";
		s.global = false;
	}
});

// Bind script tag hack transport
jQuery.ajaxTransport( "script", function(s) {

	// This transport only deals with cross domain requests
	if ( s.crossDomain ) {

		var script,
			head = document.head || jQuery("head")[0] || document.documentElement;

		return {

			send: function( _, callback ) {

				script = document.createElement("script");

				script.async = true;

				if ( s.scriptCharset ) {
					script.charset = s.scriptCharset;
				}

				script.src = s.url;

				// Attach handlers for all browsers
				script.onload = script.onreadystatechange = function( _, isAbort ) {

					if ( isAbort || !script.readyState || /loaded|complete/.test( script.readyState ) ) {

						// Handle memory leak in IE
						script.onload = script.onreadystatechange = null;

						// Remove the script
						if ( script.parentNode ) {
							script.parentNode.removeChild( script );
						}

						// Dereference the script
						script = null;

						// Callback if not abort
						if ( !isAbort ) {
							callback( 200, "success" );
						}
					}
				};

				// Circumvent IE6 bugs with base elements (#2709 and #4378) by prepending
				// Use native DOM manipulation to avoid our domManip AJAX trickery
				head.insertBefore( script, head.firstChild );
			},

			abort: function() {
				if ( script ) {
					script.onload( undefined, true );
				}
			}
		};
	}
});




var oldCallbacks = [],
	rjsonp = /(=)\?(?=&|$)|\?\?/;

// Default jsonp settings
jQuery.ajaxSetup({
	jsonp: "callback",
	jsonpCallback: function() {
		var callback = oldCallbacks.pop() || ( jQuery.expando + "_" + ( nonce++ ) );
		this[ callback ] = true;
		return callback;
	}
});

// Detect, normalize options and install callbacks for jsonp requests
jQuery.ajaxPrefilter( "json jsonp", function( s, originalSettings, jqXHR ) {

	var callbackName, overwritten, responseContainer,
		jsonProp = s.jsonp !== false && ( rjsonp.test( s.url ) ?
			"url" :
			typeof s.data === "string" && !( s.contentType || "" ).indexOf("application/x-www-form-urlencoded") && rjsonp.test( s.data ) && "data"
		);

	// Handle iff the expected data type is "jsonp" or we have a parameter to set
	if ( jsonProp || s.dataTypes[ 0 ] === "jsonp" ) {

		// Get callback name, remembering preexisting value associated with it
		callbackName = s.jsonpCallback = jQuery.isFunction( s.jsonpCallback ) ?
			s.jsonpCallback() :
			s.jsonpCallback;

		// Insert callback into url or form data
		if ( jsonProp ) {
			s[ jsonProp ] = s[ jsonProp ].replace( rjsonp, "$1" + callbackName );
		} else if ( s.jsonp !== false ) {
			s.url += ( rquery.test( s.url ) ? "&" : "?" ) + s.jsonp + "=" + callbackName;
		}

		// Use data converter to retrieve json after script execution
		s.converters["script json"] = function() {
			if ( !responseContainer ) {
				jQuery.error( callbackName + " was not called" );
			}
			return responseContainer[ 0 ];
		};

		// force json dataType
		s.dataTypes[ 0 ] = "json";

		// Install callback
		overwritten = window[ callbackName ];
		window[ callbackName ] = function() {
			responseContainer = arguments;
		};

		// Clean-up function (fires after converters)
		jqXHR.always(function() {
			// Restore preexisting value
			window[ callbackName ] = overwritten;

			// Save back as free
			if ( s[ callbackName ] ) {
				// make sure that re-using the options doesn't screw things around
				s.jsonpCallback = originalSettings.jsonpCallback;

				// save the callback name for future use
				oldCallbacks.push( callbackName );
			}

			// Call if it was a function and we have a response
			if ( responseContainer && jQuery.isFunction( overwritten ) ) {
				overwritten( responseContainer[ 0 ] );
			}

			responseContainer = overwritten = undefined;
		});

		// Delegate to script
		return "script";
	}
});




// data: string of html
// context (optional): If specified, the fragment will be created in this context, defaults to document
// keepScripts (optional): If true, will include scripts passed in the html string
jQuery.parseHTML = function( data, context, keepScripts ) {
	if ( !data || typeof data !== "string" ) {
		return null;
	}
	if ( typeof context === "boolean" ) {
		keepScripts = context;
		context = false;
	}
	context = context || document;

	var parsed = rsingleTag.exec( data ),
		scripts = !keepScripts && [];

	// Single tag
	if ( parsed ) {
		return [ context.createElement( parsed[1] ) ];
	}

	parsed = jQuery.buildFragment( [ data ], context, scripts );

	if ( scripts && scripts.length ) {
		jQuery( scripts ).remove();
	}

	return jQuery.merge( [], parsed.childNodes );
};


// Keep a copy of the old load method
var _load = jQuery.fn.load;

/**
 * Load a url into a page
 */
jQuery.fn.load = function( url, params, callback ) {
	if ( typeof url !== "string" && _load ) {
		return _load.apply( this, arguments );
	}

	var selector, response, type,
		self = this,
		off = url.indexOf(" ");

	if ( off >= 0 ) {
		selector = jQuery.trim( url.slice( off, url.length ) );
		url = url.slice( 0, off );
	}

	// If it's a function
	if ( jQuery.isFunction( params ) ) {

		// We assume that it's the callback
		callback = params;
		params = undefined;

	// Otherwise, build a param string
	} else if ( params && typeof params === "object" ) {
		type = "POST";
	}

	// If we have elements to modify, make the request
	if ( self.length > 0 ) {
		jQuery.ajax({
			url: url,

			// if "type" variable is undefined, then "GET" method will be used
			type: type,
			dataType: "html",
			data: params
		}).done(function( responseText ) {

			// Save response for use in complete callback
			response = arguments;

			self.html( selector ?

				// If a selector was specified, locate the right elements in a dummy div
				// Exclude scripts to avoid IE 'Permission Denied' errors
				jQuery("<div>").append( jQuery.parseHTML( responseText ) ).find( selector ) :

				// Otherwise use the full result
				responseText );

		}).complete( callback && function( jqXHR, status ) {
			self.each( callback, response || [ jqXHR.responseText, status, jqXHR ] );
		});
	}

	return this;
};




jQuery.expr.filters.animated = function( elem ) {
	return jQuery.grep(jQuery.timers, function( fn ) {
		return elem === fn.elem;
	}).length;
};





var docElem = window.document.documentElement;

/**
 * Gets a window from an element
 */
function getWindow( elem ) {
	return jQuery.isWindow( elem ) ?
		elem :
		elem.nodeType === 9 ?
			elem.defaultView || elem.parentWindow :
			false;
}

jQuery.offset = {
	setOffset: function( elem, options, i ) {
		var curPosition, curLeft, curCSSTop, curTop, curOffset, curCSSLeft, calculatePosition,
			position = jQuery.css( elem, "position" ),
			curElem = jQuery( elem ),
			props = {};

		// set position first, in-case top/left are set even on static elem
		if ( position === "static" ) {
			elem.style.position = "relative";
		}

		curOffset = curElem.offset();
		curCSSTop = jQuery.css( elem, "top" );
		curCSSLeft = jQuery.css( elem, "left" );
		calculatePosition = ( position === "absolute" || position === "fixed" ) &&
			jQuery.inArray("auto", [ curCSSTop, curCSSLeft ] ) > -1;

		// need to be able to calculate position if either top or left is auto and position is either absolute or fixed
		if ( calculatePosition ) {
			curPosition = curElem.position();
			curTop = curPosition.top;
			curLeft = curPosition.left;
		} else {
			curTop = parseFloat( curCSSTop ) || 0;
			curLeft = parseFloat( curCSSLeft ) || 0;
		}

		if ( jQuery.isFunction( options ) ) {
			options = options.call( elem, i, curOffset );
		}

		if ( options.top != null ) {
			props.top = ( options.top - curOffset.top ) + curTop;
		}
		if ( options.left != null ) {
			props.left = ( options.left - curOffset.left ) + curLeft;
		}

		if ( "using" in options ) {
			options.using.call( elem, props );
		} else {
			curElem.css( props );
		}
	}
};

jQuery.fn.extend({
	offset: function( options ) {
		if ( arguments.length ) {
			return options === undefined ?
				this :
				this.each(function( i ) {
					jQuery.offset.setOffset( this, options, i );
				});
		}

		var docElem, win,
			box = { top: 0, left: 0 },
			elem = this[ 0 ],
			doc = elem && elem.ownerDocument;

		if ( !doc ) {
			return;
		}

		docElem = doc.documentElement;

		// Make sure it's not a disconnected DOM node
		if ( !jQuery.contains( docElem, elem ) ) {
			return box;
		}

		// If we don't have gBCR, just use 0,0 rather than error
		// BlackBerry 5, iOS 3 (original iPhone)
		if ( typeof elem.getBoundingClientRect !== strundefined ) {
			box = elem.getBoundingClientRect();
		}
		win = getWindow( doc );
		return {
			top: box.top  + ( win.pageYOffset || docElem.scrollTop )  - ( docElem.clientTop  || 0 ),
			left: box.left + ( win.pageXOffset || docElem.scrollLeft ) - ( docElem.clientLeft || 0 )
		};
	},

	position: function() {
		if ( !this[ 0 ] ) {
			return;
		}

		var offsetParent, offset,
			parentOffset = { top: 0, left: 0 },
			elem = this[ 0 ];

		// fixed elements are offset from window (parentOffset = {top:0, left: 0}, because it is its only offset parent
		if ( jQuery.css( elem, "position" ) === "fixed" ) {
			// we assume that getBoundingClientRect is available when computed position is fixed
			offset = elem.getBoundingClientRect();
		} else {
			// Get *real* offsetParent
			offsetParent = this.offsetParent();

			// Get correct offsets
			offset = this.offset();
			if ( !jQuery.nodeName( offsetParent[ 0 ], "html" ) ) {
				parentOffset = offsetParent.offset();
			}

			// Add offsetParent borders
			parentOffset.top  += jQuery.css( offsetParent[ 0 ], "borderTopWidth", true );
			parentOffset.left += jQuery.css( offsetParent[ 0 ], "borderLeftWidth", true );
		}

		// Subtract parent offsets and element margins
		// note: when an element has margin: auto the offsetLeft and marginLeft
		// are the same in Safari causing offset.left to incorrectly be 0
		return {
			top:  offset.top  - parentOffset.top - jQuery.css( elem, "marginTop", true ),
			left: offset.left - parentOffset.left - jQuery.css( elem, "marginLeft", true)
		};
	},

	offsetParent: function() {
		return this.map(function() {
			var offsetParent = this.offsetParent || docElem;

			while ( offsetParent && ( !jQuery.nodeName( offsetParent, "html" ) && jQuery.css( offsetParent, "position" ) === "static" ) ) {
				offsetParent = offsetParent.offsetParent;
			}
			return offsetParent || docElem;
		});
	}
});

// Create scrollLeft and scrollTop methods
jQuery.each( { scrollLeft: "pageXOffset", scrollTop: "pageYOffset" }, function( method, prop ) {
	var top = /Y/.test( prop );

	jQuery.fn[ method ] = function( val ) {
		return access( this, function( elem, method, val ) {
			var win = getWindow( elem );

			if ( val === undefined ) {
				return win ? (prop in win) ? win[ prop ] :
					win.document.documentElement[ method ] :
					elem[ method ];
			}

			if ( win ) {
				win.scrollTo(
					!top ? val : jQuery( win ).scrollLeft(),
					top ? val : jQuery( win ).scrollTop()
				);

			} else {
				elem[ method ] = val;
			}
		}, method, val, arguments.length, null );
	};
});

// Add the top/left cssHooks using jQuery.fn.position
// Webkit bug: https://bugs.webkit.org/show_bug.cgi?id=29084
// getComputedStyle returns percent when specified for top/left/bottom/right
// rather than make the css module depend on the offset module, we just check for it here
jQuery.each( [ "top", "left" ], function( i, prop ) {
	jQuery.cssHooks[ prop ] = addGetHookIf( support.pixelPosition,
		function( elem, computed ) {
			if ( computed ) {
				computed = curCSS( elem, prop );
				// if curCSS returns percentage, fallback to offset
				return rnumnonpx.test( computed ) ?
					jQuery( elem ).position()[ prop ] + "px" :
					computed;
			}
		}
	);
});


// Create innerHeight, innerWidth, height, width, outerHeight and outerWidth methods
jQuery.each( { Height: "height", Width: "width" }, function( name, type ) {
	jQuery.each( { padding: "inner" + name, content: type, "": "outer" + name }, function( defaultExtra, funcName ) {
		// margin is only for outerHeight, outerWidth
		jQuery.fn[ funcName ] = function( margin, value ) {
			var chainable = arguments.length && ( defaultExtra || typeof margin !== "boolean" ),
				extra = defaultExtra || ( margin === true || value === true ? "margin" : "border" );

			return access( this, function( elem, type, value ) {
				var doc;

				if ( jQuery.isWindow( elem ) ) {
					// As of 5/8/2012 this will yield incorrect results for Mobile Safari, but there
					// isn't a whole lot we can do. See pull request at this URL for discussion:
					// https://github.com/jquery/jquery/pull/764
					return elem.document.documentElement[ "client" + name ];
				}

				// Get document width or height
				if ( elem.nodeType === 9 ) {
					doc = elem.documentElement;

					// Either scroll[Width/Height] or offset[Width/Height] or client[Width/Height], whichever is greatest
					// unfortunately, this causes bug #3838 in IE6/8 only, but there is currently no good, small way to fix it.
					return Math.max(
						elem.body[ "scroll" + name ], doc[ "scroll" + name ],
						elem.body[ "offset" + name ], doc[ "offset" + name ],
						doc[ "client" + name ]
					);
				}

				return value === undefined ?
					// Get width or height on the element, requesting but not forcing parseFloat
					jQuery.css( elem, type, extra ) :

					// Set width or height on the element
					jQuery.style( elem, type, value, extra );
			}, type, chainable ? margin : undefined, chainable, null );
		};
	});
});


// The number of elements contained in the matched element set
jQuery.fn.size = function() {
	return this.length;
};

jQuery.fn.andSelf = jQuery.fn.addBack;




// Register as a named AMD module, since jQuery can be concatenated with other
// files that may use define, but not via a proper concatenation script that
// understands anonymous AMD modules. A named AMD is safest and most robust
// way to register. Lowercase jquery is used because AMD module names are
// derived from file names, and jQuery is normally delivered in a lowercase
// file name. Do this after creating the global so that if an AMD module wants
// to call noConflict to hide this version of jQuery, it will work.

// Note that for maximum portability, libraries that are not jQuery should
// declare themselves as anonymous modules, and avoid setting a global if an
// AMD loader is present. jQuery is a special case. For more information, see
// https://github.com/jrburke/requirejs/wiki/Updating-existing-libraries#wiki-anon

if ( typeof define === "function" && define.amd ) {
	define( "jquery", [], function() {
		return jQuery;
	});
}




var
	// Map over jQuery in case of overwrite
	_jQuery = window.jQuery,

	// Map over the $ in case of overwrite
	_$ = window.$;

jQuery.noConflict = function( deep ) {
	if ( window.$ === jQuery ) {
		window.$ = _$;
	}

	if ( deep && window.jQuery === jQuery ) {
		window.jQuery = _jQuery;
	}

	return jQuery;
};

// Expose jQuery and $ identifiers, even in
// AMD (#7102#comment:10, https://github.com/jquery/jquery/pull/557)
// and CommonJS for browser emulators (#13566)
if ( typeof noGlobal === strundefined ) {
	window.jQuery = window.$ = jQuery;
}




return jQuery;

}));

define('hv/util/log',[],function() {

	var log = function f() {
			log.history = log.history || [];
			log.history.push(arguments);
			if (this.console) {
				var args = arguments,
					newarr;
				args.callee = args.callee.caller;
				newarr = [].slice.call(args);
				if (typeof console.log === 'object') log.apply.call(console.log, console, newarr);
				else console.log.apply(console, newarr);
			}
		};

	return log;

});

define('app/Config',['jquery'], function($){
	var defaultConfig = {

		root: location.href.substr(0,location.href.lastIndexOf('/')+1),

		imgPathBgMountains: "../img/bgimg/bg-mountains-back.png",
		imgPathBgMountain: "../img/bgimg/bg-mountains-front.png",
		imgPathBgBack: "../img/bgimg/bg-back3-1.jpg",
		imgPathBgLeft: "../img/bgimg/bg-left-blur.png",
		imgPathBgRight: "../img/bgimg/bg-right-blur.png",
		imgPathBgRoute: "../img/bgimg/bg-route.png",
		imgPathBgLevel: "../img/bgimg/bg-level.png",

		randomClouds: ["../img/world3d/cloud1.png", "../img/world3d/cloud2.png", "../img/world3d/cloud3.png"],

		langThemerouteNext:"Weiter auf Route - %themeRouteName%",
		langThemeroutePrev:"Zurück auf Route - %themeRouteName%",

		errorPageOldBrowser: "various-old-browser.html",
		errorPageMobile: "various-mobile.html",

		langVideoMute: "Mute",
		langVideoUnmute: "Unmute",
		langVideoPlay: "Play",
		langVideoPause: "Pause"

	};

	var config = $.extend({}, defaultConfig, window.app_config);

	return {
		get: function(key) { return config[key]; },
		set: function(key, value) { config[key] = value; }
	};
});

define('app/credits',[], function(){

	var credits = '';

	credits += "            +++++++++                                               " + "\n";
	credits += "           ++++++++++                                               " + "\n";
	credits += "          ++++++++++,   ;++++; +++   +++   +++ ++;  +++++.   +++++`       " + "\n";
	credits += "         :+;  ;+++++   ;++''++:,++   +++   ++; ++; +++;+++  +++;+++               _" + "\n";
	credits += "        `++;  ;+++++   +++  +++ ++  .+++:  ++  ++; ++.  ++: ++`  ++,            -=\\`\\" + "\n";
	credits += "        +++;  ;+++++   +++:     ++; ++,++ .++  ++; +++.     +++`            |\\ ____\\_\\__" + "\n";
	credits += "       +          +,    +++++`  '++ ++ ++ +++  ++; :+++++   ;+++++        -=\\c`\"\"\"\"\"\"\" \"`)" + "\n";
	credits += "      ++          +      '++++:  ++ ++ ++.++,  ++;   +++++    +++++          `~~~~~/ /~~`" + "\n";
	credits += "     ;++          +         +++  ++'+; ,++++   ++;     `+++     .++'           -==/ /" + "\n";
	credits += "    ,++++++;  ;++++    ++:  '++  ++++   ++++   ++; ++   +++ ++   ++'             '-'" + "\n";
	credits += "    +++++++;  ;+++,    +++''++;  ,+++   +++'   ++; +++;+++` +++;+++       " + "\n";
	credits += "   ++++++++;  ;+++      '++++'    +++   ;++    ++;  +++++,   +++++.       " + "\n";
	credits += "  ++++++++++++++++                                                  " + "\n";
	credits += " '++++++++++++++++                                                  ";
	console.log('%c ' + credits, 'background: #FFF; color: #c00');

	var credits2 = '';
	credits2 += "                      made with love by                          " + "\n";
	credits2 += "                       Hinderling Volkart – hinderlingvolkart.com " + "\n";

	console.log('%c ' + credits2, 'background: #0098cf; color: #FFF');

	return credits;
});




define('app/plugins',['app/credits'], function(){
	return true;
});




/*!
 * jQuery Mousewheel 3.1.13
 *
 * Copyright jQuery Foundation and other contributors
 * Released under the MIT license
 * http://jquery.org/license
 */


(function (factory) {
    if ( typeof define === 'function' && define.amd ) {
        // AMD. Register as an anonymous module.
        define('mousewheel',['jquery'], factory);
    } else if (typeof exports === 'object') {
        // Node/CommonJS style for Browserify
        module.exports = factory;
    } else {
        // Browser globals
        factory(jQuery);
    }
}(function ($) {

    var toFix  = ['wheel', 'mousewheel', 'DOMMouseScroll', 'MozMousePixelScroll'],
        toBind = ( 'onwheel' in document || document.documentMode >= 9 ) ?
                    ['wheel'] : ['mousewheel', 'DomMouseScroll', 'MozMousePixelScroll'],
        slice  = Array.prototype.slice,
        nullLowestDeltaTimeout, lowestDelta;

    if ( $.event.fixHooks ) {
        for ( var i = toFix.length; i; ) {
            $.event.fixHooks[ toFix[--i] ] = $.event.mouseHooks;
        }
    }

    var special = $.event.special.mousewheel = {
        version: '3.1.12',

        setup: function() {
            if ( this.addEventListener ) {
                for ( var i = toBind.length; i; ) {
                    this.addEventListener( toBind[--i], handler, false );
                }
            } else {
                this.onmousewheel = handler;
            }
            // Store the line height and page height for this particular element
            $.data(this, 'mousewheel-line-height', special.getLineHeight(this));
            $.data(this, 'mousewheel-page-height', special.getPageHeight(this));
        },

        teardown: function() {
            if ( this.removeEventListener ) {
                for ( var i = toBind.length; i; ) {
                    this.removeEventListener( toBind[--i], handler, false );
                }
            } else {
                this.onmousewheel = null;
            }
            // Clean up the data we added to the element
            $.removeData(this, 'mousewheel-line-height');
            $.removeData(this, 'mousewheel-page-height');
        },

        getLineHeight: function(elem) {
            var $elem = $(elem),
                $parent = $elem['offsetParent' in $.fn ? 'offsetParent' : 'parent']();
            if (!$parent.length) {
                $parent = $('body');
            }
            return parseInt($parent.css('fontSize'), 10) || parseInt($elem.css('fontSize'), 10) || 16;
        },

        getPageHeight: function(elem) {
            return $(elem).height();
        },

        settings: {
            adjustOldDeltas: true, // see shouldAdjustOldDeltas() below
            normalizeOffset: true  // calls getBoundingClientRect for each event
        }
    };

    $.fn.extend({
        mousewheel: function(fn) {
            return fn ? this.bind('mousewheel', fn) : this.trigger('mousewheel');
        },

        unmousewheel: function(fn) {
            return this.unbind('mousewheel', fn);
        }
    });


    function handler(event) {
        var orgEvent   = event || window.event,
            args       = slice.call(arguments, 1),
            delta      = 0,
            deltaX     = 0,
            deltaY     = 0,
            absDelta   = 0,
            offsetX    = 0,
            offsetY    = 0;
        event = $.event.fix(orgEvent);
        event.type = 'mousewheel';

        // Old school scrollwheel delta
        if ( 'detail'      in orgEvent ) { deltaY = orgEvent.detail * -1;      }
        if ( 'wheelDelta'  in orgEvent ) { deltaY = orgEvent.wheelDelta;       }
        if ( 'wheelDeltaY' in orgEvent ) { deltaY = orgEvent.wheelDeltaY;      }
        if ( 'wheelDeltaX' in orgEvent ) { deltaX = orgEvent.wheelDeltaX * -1; }

        // Firefox < 17 horizontal scrolling related to DOMMouseScroll event
        if ( 'axis' in orgEvent && orgEvent.axis === orgEvent.HORIZONTAL_AXIS ) {
            deltaX = deltaY * -1;
            deltaY = 0;
        }

        // Set delta to be deltaY or deltaX if deltaY is 0 for backwards compatabilitiy
        delta = deltaY === 0 ? deltaX : deltaY;

        // New school wheel delta (wheel event)
        if ( 'deltaY' in orgEvent ) {
            deltaY = orgEvent.deltaY * -1;
            delta  = deltaY;
        }
        if ( 'deltaX' in orgEvent ) {
            deltaX = orgEvent.deltaX;
            if ( deltaY === 0 ) { delta  = deltaX * -1; }
        }

        // No change actually happened, no reason to go any further
        if ( deltaY === 0 && deltaX === 0 ) { return; }

        // Need to convert lines and pages to pixels if we aren't already in pixels
        // There are three delta modes:
        //   * deltaMode 0 is by pixels, nothing to do
        //   * deltaMode 1 is by lines
        //   * deltaMode 2 is by pages
        if ( orgEvent.deltaMode === 1 ) {
            var lineHeight = $.data(this, 'mousewheel-line-height');
            delta  *= lineHeight;
            deltaY *= lineHeight;
            deltaX *= lineHeight;
        } else if ( orgEvent.deltaMode === 2 ) {
            var pageHeight = $.data(this, 'mousewheel-page-height');
            delta  *= pageHeight;
            deltaY *= pageHeight;
            deltaX *= pageHeight;
        }

        // Store lowest absolute delta to normalize the delta values
        absDelta = Math.max( Math.abs(deltaY), Math.abs(deltaX) );

        if ( !lowestDelta || absDelta < lowestDelta ) {
            lowestDelta = absDelta;

            // Adjust older deltas if necessary
            if ( shouldAdjustOldDeltas(orgEvent, absDelta) ) {
                lowestDelta /= 40;
            }
        }

        // Adjust older deltas if necessary
        if ( shouldAdjustOldDeltas(orgEvent, absDelta) ) {
            // Divide all the things by 40!
            delta  /= 40;
            deltaX /= 40;
            deltaY /= 40;
        }

        // Get a whole, normalized value for the deltas
        delta  = Math[ delta  >= 1 ? 'floor' : 'ceil' ](delta  / lowestDelta);
        deltaX = Math[ deltaX >= 1 ? 'floor' : 'ceil' ](deltaX / lowestDelta);
        deltaY = Math[ deltaY >= 1 ? 'floor' : 'ceil' ](deltaY / lowestDelta);

        // Normalise offsetX and offsetY properties
        if ( special.settings.normalizeOffset && this.getBoundingClientRect ) {
            var boundingRect = this.getBoundingClientRect();
            offsetX = event.clientX - boundingRect.left;
            offsetY = event.clientY - boundingRect.top;
        }

        // Add information to the event object
        event.deltaX = deltaX;
        event.deltaY = deltaY;
        event.deltaFactor = lowestDelta;
        event.offsetX = offsetX;
        event.offsetY = offsetY;
        // Go ahead and set deltaMode to 0 since we converted to pixels
        // Although this is a little odd since we overwrite the deltaX/Y
        // properties with normalized deltas.
        event.deltaMode = 0;

        // Add event and delta to the front of the arguments
        args.unshift(event, delta, deltaX, deltaY);

        // Clearout lowestDelta after sometime to better
        // handle multiple device types that give different
        // a different lowestDelta
        // Ex: trackpad = 3 and mouse wheel = 120
        if (nullLowestDeltaTimeout) { clearTimeout(nullLowestDeltaTimeout); }
        nullLowestDeltaTimeout = setTimeout(nullLowestDelta, 200);

        return ($.event.dispatch || $.event.handle).apply(this, args);
    }

    function nullLowestDelta() {
        lowestDelta = null;
    }

    function shouldAdjustOldDeltas(orgEvent, absDelta) {
        // If this is an older event and the delta is divisable by 120,
        // then we are assuming that the browser is treating this as an
        // older mouse wheel event and that we should divide the deltas
        // by 40 to try and get a more usable deltaFactor.
        // Side note, this actually impacts the reported scroll distance
        // in older browsers and can cause scrolling to be slower than native.
        // Turn this off by setting $.event.special.mousewheel.settings.adjustOldDeltas to false.
        return special.settings.adjustOldDeltas && orgEvent.type === 'mousewheel' && absDelta % 120 === 0;
    }

}));

/*
 * contextTrigger
 *
 * Binds functions to a certain context that is defined by a DOM Element.
 *
 * Usage:
 *
 * contextTrigger.add( triggerSelector,callback );
 *
 *
 * ---------------------------------------------------------------------------
 *
 * Example:
 *
 * contextTrigger.add("#main", function(){
 *
 *  require(['uxui/util/Frameplayer'], function(F){
 *    console.log(F);
 *  });
 *
 * });
 *
 */


define('lib/util/contextTrigger',['jquery'], function() {

	var contextTrigger;

	contextTrigger = {
		events: {}
	};

	contextTrigger.add = function(selector, func){

		if (!contextTrigger.events[ selector ]){
			contextTrigger.events[ selector ] = [];
		}

		contextTrigger.events[ selector ].push(func);

		//$(selector).each(func);
	};

	contextTrigger.remove = function(selector, func){
		if (!contextTrigger.events[selector]){
			return false;
		}

		if (!func){
			contextTrigger.events[selector] = null;
		}else {
			for (var evnt in contextTrigger.events[selector]){
				if (contextTrigger.events[selector][evnt] === func){
					contextTrigger.events[selector][evnt] = null;
				}
			}
		}
	};

	contextTrigger.run = function(context){
		// override
		//contextTrigger.validate(context);
	};

	contextTrigger.validate = function(element){
		var evnt, $element;
		var selector, $selector;
		element = element || 'body';

		$element = $(element);

		function callback(){
			if (!this.contextTriggerProcessed) {
				contextTrigger.events[selector][evnt].call(this, this);
			}
		}

		if (!$element.length){
			return false;
		}

		for (selector in contextTrigger.events){

			$selector = $element.find(selector);
			if ($element.is(selector)) {
				$selector = $selector.add(element);
			}

			if ($selector.length){
				for (evnt in contextTrigger.events[selector]) {
					$selector.each(callback);
				}
			}
		}

		markAsProcessed($element.add($element.find('*')));

		//console.log("Processing", $element.length, "took", new Date() - t, 'ms');
	};


	function checkNode(node, result) {
		if (!node.contextTriggerProcessed) {
			result.push(node);
		} else {
			var c = node.firstChild;
			while (c) {
				if (c.nodeType === 1) {
					checkNode(c, result);
				}
				c = c.nextSibling;
			}
		}
	}

	function checkForNewElements() {
		// first we loop through all dom elements to see if we find at least
		// one element that's not processed yet
		var i;
		var all = document.body.querySelectorAll('*');
		var len = all.length;
		var any = false;
		for (i = 0; i < len; i++) {
			if (!all[i].contextTriggerProcessed) {
				any = true;
				break;
			}
		}
		if (!any) return;

		// only if we find at least one element we're going into the more
		// costly evaluation to find the top elements inserted and process those
		var found = [];
		checkNode(document.body, found);

		for (i = 0; i < found.length; i++) {
			contextTrigger.validate(found[i]);
		}
	}

	function markAsProcessed(elements) {
		var i, len = elements.length;
		for (i = 0; i < len; i++) {
			elements[i].contextTriggerProcessed = true;
		}
	}

	if (window.MutationObserver) {
		$(function(){
			var target = window.document.body;
			var observer = new MutationObserver(function(mutations) {
				var i, len = mutations.length;
				for (i = 0; i < len; i++) {
					if (mutations[i].addedNodes.length) {
						invalidate();
						break;
					}
				}
			});
			var config = { subtree: true, childList: true };
			observer.observe(target, config);

			var timeout;
			function invalidate(){
				clearTimeout(timeout);
				timeout = setTimeout(validate, 50);
			}
			function validate(){
				clearTimeout(timeout);
				checkForNewElements();
			}
		});
	} else {
		setInterval(checkForNewElements, 1000);
	}

	return contextTrigger;

});

define(
'lib/util/ModuleManager',[
	'lib/util/contextTrigger'
],
function(
	contextTrigger
){

	// every module should at least implement two methods
	// Module.init = function( HTMLElement )
	// Module.destroy = function()
	//
	// Modules are per se site specific (if necessary).

	var moduleInstances = [];


	var garbageCollectedOnInitialise = false;




	function initialiseModul(Module, element) {
		// we want old modules garbaged before creating new ones
		if (!garbageCollectedOnInitialise) {
			checkModuleGarbage();
			garbageCollectedOnInitialise = true;
			setTimeout(function(){
				garbageCollectedOnInitialise = false;
			}, 0);
		}

		var module, moduleInstance;
		measureStart();

		// try {
		module = new Module();
		moduleInstance = module.init(element);
		var $element;
		if (moduleInstance) {
			$element = $(element);
			$element.data('moduleInstance', moduleInstance);
			moduleInstance.___el = element;
			moduleInstances.push(moduleInstance);
			$(element).attr('data-has-module', 'yes');
		}

		// } catch (error) {
		// 	console.error(error.message, error);
		// }

		measureStop(moduleInstance ? moduleInstance.ns : (module ? module.ns : 'unknown module'), element);
	}



	function checkModuleGarbage(){
		var elem, inst, len = moduleInstances.length;
		for (var i = len - 1; i >= 0; i--) {
			inst = moduleInstances[i];
			elem = inst.___el;
			if (!jQuery.contains(document.documentElement, elem)) {
				try {
					inst.___el = null;
					inst.destroy();
				} catch (e){}
				moduleInstances.splice(i, 1);
			}
		}
	}

	// an interval to check wether element have been removed from dom
	// if so, we'll find the module instance and call its destroy method
	if (window.MutationObserver) {
		$(function(){
			var target = window.document.body;
			var observer = new MutationObserver(function(mutations) {
				var i, len = mutations.length;
				for (i = 0; i < len; i++) {
					if (mutations[i].removedNodes.length) {
						invalidate();
						break;
					}
				}
			});
			var config = { subtree: true, childList: true };
			observer.observe(target, config);

			var timeout;
			function invalidate(){
				clearTimeout(timeout);
				timeout = setTimeout(validate, 50);
			}
			function validate(){
				clearTimeout(timeout);
				checkModuleGarbage();
			}
		});
	} else {
		setInterval(checkModuleGarbage, 2500);
	}




	var measureTime, totalTime = 0, measureTable = [];
	function now(){
		return window.performance && performance.now ? performance.now() : new Date();
	}
	function measureStart(){
		measureTime = now();
	}
	function measureStop(name, element){
		totalTime += now() - measureTime;
		measureTable.push({ 'Module': name, 'Element': element, 'Time (ms)': Math.round((now() - measureTime) * 10) / 10 });
	}

	setTimeout(function(){
		console.log('Module init took ' + totalTime.toFixed(1) + ' ms');
		if (console.table && measureTable.length > 0) {
			console.table(measureTable);
		}
		measureTable = [];
	}, 5000);




	return {
		connect: function(Module, element) {
			initialiseModul(Module, element);
		},
		add: function(M, selector) {
			if (typeof Module === 'string') {
				contextTrigger.add(selector, function(){
					var elem = this;
					require([M], function(Module){
						initialiseModul(Module, elem);
					});
				});
			} else {
				contextTrigger.add(selector, function(){
					var elem = this;
					initialiseModul(M, elem);
				});
			}
		},
		checkGarbage: checkModuleGarbage
	};
}


);

define(
'app/content/BaseModule',[
	'jquery'
],
function(
	$
){

	var Module;
	var ns = '.module-module'; // CHANGE THIS!

	Module = function(){
	};

	Module.prototype.destroy = Module.prototype._destroy = function(){
		$(document).off(this.ns);
		$(window).off(this.ns);
	};


	Module.prototype.bind = function(method) {
		var self = this;
		return function(){
			method.apply(self, arguments);
		};
	};


	return Module;
});

define('hv/animation/AnimationFrame',[],function(){

	var lastTime = 0;
	var vendors = ['ms', 'moz', 'webkit', 'o'];

	var requestFrame = window.requestAnimationFrame;
	var cancelFrame = window.cancelAnimationFrame;

	for(var x = 0; x < vendors.length && !requestFrame; ++x) {
		requestFrame = window[vendors[x]+'RequestAnimationFrame'];
		cancelFrame = window[vendors[x]+'CancelAnimationFrame'] || window[vendors[x]+'CancelRequestAnimationFrame'];
	}

	var forceTimeout = navigator.userAgent.toLowerCase().indexOf('trident') >= 0;

	if (forceTimeout || !requestFrame) {
		requestFrame = function(callback, element) {
			var currTime = new Date().getTime();
			var timeToCall = Math.max(0, 16 - (currTime - lastTime));
			var id = window.setTimeout(function() { callback(currTime + timeToCall); }, timeToCall);
			lastTime = currTime + timeToCall;
			return id;
		};
	}

	if (forceTimeout || !cancelFrame) {
		cancelFrame = function(id) {
			clearTimeout(id);
		};
	}

	return {
		request: function(){ return requestFrame.apply(null, arguments); },
		cancel: function(){ return cancelFrame.apply(null, arguments); }
	};

});

define('hv/util/EventDispatcherNew',[],function(){

	var DEFAULT = 'd_e_f_a_u_l_t';

	function EventObserver( target, method ) {
		this.target = target;
		this.method = method;
	}
	EventObserver.prototype.call = function( params, dispatcher ) {
		if ( typeof(this.method) == 'string' ) {
			return this.target[this.method].apply(this.target||dispatcher, params);
		}
		else {
			return this.method.apply(this.target||dispatcher, params);
		}
	};
	EventObserver.prototype.isEqual = function( target, method ) {
		return this.target == target && this.method == method;
	};




	function extractNamespace(event) {
		var index = event.indexOf('.');
		if ( index >= 0 ) {
			return {
				name: event.substr(0,index),
				ns: event.substr(index+1)
			};
		} else {
			return {
				name: event, ns: DEFAULT
			};
		}
	}

	function _index( observers, target, method ) {
		for (var i = observers.length - 1; i >= 0; i--) {
			if ( observers[i].isEqual(target, method) ) {
				return i;
			}
		}
		return -1;
	}

	function _removeEventListener(observers, target, method) {
		var i;
		if ( !observers ) {
			return;
		}
		if ( method ) {
			i = _index(observers, target, method);
			if ( i >=0 ) {
				observers.splice(i, 1);
			}
		} else {
			for (i = observers.length - 1; i >= 0; i--) {
				if ( !target || observers[i].target == target ) {
					observers.splice(i, 1);
				}
			}
		}
	}





	/**
	 * EventDispatcher
	 *
	 * @author Severin Klaus, Hinderling Volkart AG
	 */

	function EventDispatcher() {
	}

	EventDispatcher.prototype.addEventListener = function(event, closure, target) {
		var e = extractNamespace(event);
		var observer, index, observers;
		if(typeof this.eventListeners == 'undefined') {
			this.eventListeners = {};
		}
		if(typeof this.eventListeners[e.name] == 'undefined') {
			this.eventListeners[e.name] = {};
		}
		if(typeof this.eventListeners[e.name][e.ns] == 'undefined') {
			this.eventListeners[e.name][e.ns] = [];
		}
		observers = this.eventListeners[e.name][e.ns];
		index = _index(observers, target, closure);
		if ( index < 0 ) {
			observer = new EventObserver(target, closure);
			observers.push( observer );
		}
		return observer;
	};

	EventDispatcher.prototype.removeEventListener = function(event, closure, target) {
		var i, listeners;

		if(typeof this.eventListeners == 'undefined') {
			this.eventListeners = {};
		}

		if ( !event ) {
			for ( i in this.eventListeners ) {
				this.removeEventListener(i, closure, target);
			}
			return;
		}

		var e = extractNamespace(event);
		var name = e.name, ns = e.ns;

		if ( !name && ns ) {
			for ( i in this.eventListeners ) {
				_removeEventListener( this.eventListeners[i][ns], target, closure );
			}
			return;
		}

		listeners = this.eventListeners[name];

		if ( !closure && !target ) {
			if ( ns !== DEFAULT ) {
				listeners[ns] = [];
			}
			else {
				this.eventListeners[name] = {};
			}
		} else {
			if ( ns !== DEFAULT ) {
				_removeEventListener( listeners[ns], target, closure );
			}
			else {
				for ( i in listeners ) {
					_removeEventListener( listeners[i], target, closure );
				}
			}
		}
	};

	EventDispatcher.prototype.removeAllEventListeners = function(value) {
		if ( typeof(value) == 'string' ) {
			this.removeEventListener(value);
		} else {
			this.removeEventListenersOf(value);
		}
	};

	EventDispatcher.prototype.removeEventListenersOf = function(target) {
		this.removeEventListener(null, null, target);
	};

	// return false to return false, return anything else (0, '', true, {}, undefined) for true
	EventDispatcher.prototype.trigger = function(event) {
		var i, params = [];
		for ( i=1; i<arguments.length; i++) {
			params.push(arguments[i]);
		}
		var observers, callReturn, result = true;
		if(typeof this.eventListeners == 'undefined') {
			this.eventListeners = {};
		}
		for(var ns in this.eventListeners[event]) {
			observers = this.eventListeners[event][ns];
			for (i = observers.length - 1; i >= 0; i--) {
				callReturn = observers[i].call( params, this );
				result &= (callReturn !== false);
			}
		}
		return result;
	};

	return EventDispatcher;

});

/*
 *
 *  Deferred State
 *
 *  An alternative to event listening for state changes:
 *
 * 	var states = new DeferredState(['a','b']);
 * 	states.set('a');
 * 	states.a(function(){ console.log('It is a now.'); });
 * 	// console: Its is a now.
 * 	states.b(function(){ console.log('It is b now.'); });
 * 	states.set('b');
 * 	// console: It is b now.
 *
 */

define('hv/util/DeferredState',['hv/util/EventDispatcherNew'], function(EventDispatcher){

	function addFunction(instance, state){
		instance[state] = function(callback, target){
			var observer = this.addEventListener(state, callback, target);
			if ( observer && state == this.state) {
				observer.call([this.state], this);
			}
			return this;
		};
	}

	function DeferredState(states){
		this.___states = [];
		if ( states ) {
			for (var i = states.length - 1; i >= 0; i--) {
				this.___states.push( states[i] );
				addFunction(this, states[i]);
			}
		}
	}
	DeferredState.prototype = new EventDispatcher();
	DeferredState.prototype.set = function(value){
		if ( value != this.state ) {
			this.state = value;
			this.trigger(this.state);
		}
		return this;
	};
	DeferredState.prototype.unlisten = function(callback, target){
		if ( !( typeof(callback) == 'string' || typeof(callback) == 'function') && !target ) {
			target = callback;
			this.removeEventListenersOf(target);
		} else {
			this.removeEventListener(null, callback, target);
		}
	};

	return DeferredState;
});

/*
 *
 *  Deferred Boolean
 *
 *  A Boolean only Deferred state.
 *
 */

define('hv/util/DeferredBoolean',['hv/util/DeferredState'], function(DeferredState){

	function DeferredBoolean(initialState){
		if ( typeof(initialState) !== 'undefined' ) {
			this.set(initialState);
		}
	}
	DeferredBoolean.prototype = new DeferredState(['yes','no']);
	DeferredBoolean.prototype._set = DeferredBoolean.prototype.set;
	DeferredBoolean.prototype.set = function(value){
		return this._set(value ? 'yes' : 'no');
	};
	DeferredBoolean.prototype.get = function(value){
		return this.state == 'yes';
	};
	DeferredBoolean.prototype.then = DeferredBoolean.prototype.yes;
	DeferredBoolean.prototype.otherwise = DeferredBoolean.prototype.no;

	return DeferredBoolean;
});

/*
 *
 *  MediaDispatcher
 *
 *  Notifies of media breakpoint changes (media query). Only works in conjunction with CSS.
 *  Example CSS:

	body:after {
		display: none;
		content: 'desktop';
		@include tablet {
			content: 'tablet';
		}
		@include tablet-portrait {
			content: 'tablet-portrait';
		}
		@include mobile {
			content: 'mobile';
		}
		@include mobile-portrait {
			content: 'mobile-portrait';
		}
	}

 *
 */


define('hv/browser/MediaDispatcher',['jquery', 'hv/util/DeferredBoolean'], function($, DeferredBoolean) {

	/**
	 * Usage:
	 *
	 * mediaTrigger.is('mobile').then(function(){ ... });
	 * -- triggered only when mobile
	 * mediaTrigger.isNot('tablet').then(function(){ ... });
	 * -- triggered when not tablet, so for tablet-portrait, mobile, mobile-portrait or default
	 * mediaTrigger.isOrBelow('tablet-portrait').then(function(){ ... });
	 * -- triggered when tablet-portrait, mobile, mobile-portrait
	 * mediaTrigger.isOrAbove('tablet').then(function(){ ... });
	 * -- triggered when tablet or default (desktop)
	 * mediaTrigger.isBelow('tablet-portrait').then(function(){ ... });
	 * -- triggered when mobile, mobile-portrait
	 * mediaTrigger.isAbove('mobile').then(function(){ ... });
	 * -- triggered when tablet-portrait, tablet, default (desktop)
	 * mediaTrigger.isNone().then(function(){ ... });
	 * mediaTrigger.isDefault().then(function(){ ... });
	 * -- triggered when default (desktop)
	 *
	 * Alternative syntax:
	 * mediaTrigger.is('mobile', function(){ ... });
	 *
	 */

	var $window = $(window);
	var triggers = [];
	var falseTrigger = new DeferredBoolean(false);
	var trueTrigger = new DeferredBoolean(true);

	function registerMediaTrigger(value) {
		triggers.push(value);
		value.validate();
	}

	function handleResize() {
		for (var i = triggers.length - 1; i >= 0; i--) {
			triggers[i].validate();
		}
	}
	$window.resize(handleResize);
	handleResize();



	function Trigger(name, index) {
		this.name = name;
		this.index = index;
		this.isOrBelow = new DeferredBoolean();
		this.isOrAbove = new DeferredBoolean();
		this.isExactly = new DeferredBoolean();
	}


	MediaTrigger = function(triggerPoints){
		this.element = document.body;
		this.pseudo = 'after';
		this.mediaIndex = -1;
		this.triggerPoints = [];
		if ( triggerPoints ) {
			this.setTriggerPoints(triggerPoints);
		}
		registerMediaTrigger(this);
	};


	MediaTrigger.prototype.setTriggerPoints = function(value){
		this.triggerPoints = [];
		this.triggerPoints.push( new Trigger('default',0) );
		for (var i = 0; i<value.length; i++) {
			this.triggerPoints.push( new Trigger(value[i], this.triggerPoints.length) );
		}
	};

	MediaTrigger.prototype.is = function(media, callback){
		return this._is(media, 0, 'isExactly', callback);
	};

	MediaTrigger.prototype.isOrAbove = function(media, callback){
		return this._is(media, 0, 'isOrAbove', callback);
	};

	MediaTrigger.prototype.isOrBelow = function(media, callback){
		return this._is(media, 0, 'isOrBelow', callback);
	};

	MediaTrigger.prototype.isAbove = function(media, callback){
		return this._is(media, -1, 'isOrAbove', callback);
	};

	MediaTrigger.prototype.isBelow = function(media, callback){
		return this._is(media, 1, 'isOrBelow', callback);
	};

	MediaTrigger.prototype._is = function(media, indexDiff, triggerId, callback){
		var triggerpoint = this._getTrigger(media);
		if ( !triggerpoint ) {
			throw new Error("Media Trigger point '"+media+"' doesn't exist.");
		}
		if ( indexDiff ) {
			triggerpoint = this.triggerPoints[triggerpoint.index+indexDiff];
		}
		var trigger = triggerpoint ? triggerpoint[triggerId] : falseTrigger;
		if ( callback ) {
			trigger.then(callback);
		}
		return trigger;
	};

	MediaTrigger.prototype._getTrigger = function(media){
		for (var i = this.triggerPoints.length - 1; i >= 0; i--) {
			if ( this.triggerPoints[i].name == media ) {
				return this.triggerPoints[i];
			}
		}
		return null;
	};

	MediaTrigger.prototype._setMediaIndex = function(value){
		var i, trigger, current = this.mediaIndex;
		if ( value !== current ) {
			// console.log("Media is: "+ this.triggerPoints[value].name+'/'+ value );
			this.mediaIndex = value;
			for ( i=this.triggerPoints.length-1; i>=0 ; i-- ) {
				trigger = this.triggerPoints[i];
				trigger.isOrBelow.set( i<=this.mediaIndex );
				trigger.isExactly.set( i==this.mediaIndex );
				trigger.isOrAbove.set( i>=this.mediaIndex );
			}
		}
	};

	MediaTrigger.prototype._setMedia = function(value){
		for (var i = this.triggerPoints.length - 1; i > 0; i--) {
			if ( this.triggerPoints[i].name == value ) {
				this._setMediaIndex(i);
				return;
			}
		}
		this._setMediaIndex(0);
	};

	MediaTrigger.prototype.validate = function(value){
		var cssValue;
		if ( window.getComputedStyle ) {
			cssValue = window.getComputedStyle(this.element,':'+this.pseudo).getPropertyValue('content');
			cssValue = cssValue.replace(/["']/g,'');
		}
		if ( !cssValue ) {
			cssValue = this.getFallback();
		}
		this._setMedia(cssValue);
	};

	MediaTrigger.prototype.unlisten = function(callback, target){
		for (var i = this.triggerPoints.length - 1; i >= 0; i--) {
			var p = this.triggerPoints[i];
			p.isExactly.unlisten(callback, target);
			p.isOrAbove.unlisten(callback, target);
			p.isOrBelow.unlisten(callback, target);
		}
	};


	MediaTrigger.prototype.getFallback = function(){
		if ( !this.$fallback ) {
			this.$fallback = $('<div class="media-dispatcher-fallback"></div>');
			this.$fallback.css({ position: 'absolute', left: -1000 });
			this.$fallback.appendTo('body');
			// console.log('Created MediaTrigger Fallback');
		}
		var index = parseInt( this.$fallback.css('margin-bottom'), 10);
		var point = this.triggerPoints[index];
		return point ? point.name : 'unknown';
	};

	return MediaTrigger;
});

/**
 * Instantiation of MediaDispatcher for this site. See _4.helpers.scss
 */

define('app/plugins/mediaDispatcher',['hv/browser/MediaDispatcher'], function(MediaDispatcher){
	return new MediaDispatcher(['tablet', 'tablet-portrait', 'mobile', 'mobile-portrait']);
});

/**
 * ImageCollectionContainer.
 * @selector .js-image_collection_container
 * @status enabled
*/



define (
'app/content/ImageCollectionContainer',[
	'jquery', 'app/content/BaseModule', 'hv/animation/AnimationFrame', 'app/plugins/mediaDispatcher'
],
function(
	$, BaseModule, AnimationFrame, mediaDispatcher
) {
	var ImageCollectionContainer;
	var ns = '.ImageCollectionContainer'; // CHANGE THIS!
	var instanceCounter = 0;
	var TEASER = "teaser";
	var NAVIGATION_ITEM = 'navigation item';

	var ImageCollectionContainer = function(element) {
		this.$el = null;
		this.ns = ns + (instanceCounter++);
	};

	ImageCollectionContainer.prototype = new BaseModule();

	ImageCollectionContainer.prototype.init = function( element ){
		var self = this;
		this.$el = $(element);
		this.initVariables();
		if(this.type == TEASER){
			$(document).on("world3d:currentElement"+this.ns, this.bind(this.currentElementHandler));
		}else{

			this.$el.on("mouseover"+this.ns, function(){
				if(!self.isReady && !self.isLoading){
					self.isLoading = true;
					self.loadImages(self.$collectionImages, self.$imageCollection, "image_collection--img");
				}
				self.startPlaying();
			});
			this.$el.on("mouseleave"+this.ns, function(){
				self.stopPlaying();
				if(self.currentIndex != 0){
					self.render(self.$collectionImages.eq(0));
					self.currentIndex = 0;
				}
			});
		}

		mediaDispatcher.isOrBelow('tablet').then(function(){
			$(document).off(self.ns);
			self.$el.off(self.ns);
			self.stopPlaying();
	  });
	};


	ImageCollectionContainer.prototype.currentElementHandler = function(e,data){
		if(this.level == data.level && this.id == data.id && data.visible){
			this.isActive = true;
			if(!this.isEventsBinded){
				this.bindUIActions();
			}
			if(!this.isReady && !this.isLoading){
				this.isLoading = true;
				this.loadImages(this.$collectionImages, this.$imageCollection, "image_collection--img");
			}
			if(this.type == TEASER && this.isHovered == true) return;
			this.startPlaying();
		}else{
			this.isActive = false;
			if(this.isEventsBinded){
				this.unbindUIActions();
			}
			this.stopPlaying();
		}
	}

	ImageCollectionContainer.prototype.initVariables = function() {

		this.$imageCollection = this.$el.find(".js-image_collection");
		this.$collectionImages = this.$imageCollection.find(".js-lazy_load");
		this.numberOfImages = this.$collectionImages.length;
		this.counter = this.numberOfImages;
		this.isReady = false;
		this.isLoading = false;
		this.currentIndex = 0;
		this.timer = null;
		this.isHovered = false;
		this.interval = 400;
		this.isActive = false;

		this.isEventsBinded = false;
		this.$parent = this.$el.closest(".element3dcont");
		if(this.$parent.length){
			this.level = this.$parent.data('level');
			this.id = this.$parent.attr('id');
			this.type = TEASER;
		}else{
			this.type = NAVIGATION_ITEM;
		}


		this.isPlaying = false;

	};

	ImageCollectionContainer.prototype.startPlaying = function(){
		if(!this.isPlaying){
			this.isPlaying = true;
			if(this.isReady){
				if (this.type == TEASER) this.render();
				this.startInterval();
			}
		}
	};

	ImageCollectionContainer.prototype.stopPlaying = function(){
		if(this.isPlaying){
			this.isPlaying = false;
			clearInterval(this.timer);
		}
	};

	ImageCollectionContainer.prototype.startInterval = function(){
		var self = this;
		this.timer = setInterval(function(){
			self.render();
		}, this.interval);

	}

	ImageCollectionContainer.prototype.render = function($nextImg){
		var $currImg = this.$collectionImages.eq(this.currentIndex);
		this.currentIndex++;
		if(this.currentIndex >= this.numberOfImages){
			this.currentIndex = 0;
		}
		var $nextImg = typeof $nextImg !== 'undefined' ? $nextImg : this.$collectionImages.eq(this.currentIndex);
		$nextImg.addClass('is-next');
		$currImg.show().removeClass('is-active');
 		$nextImg.removeClass('is-next').addClass('is-active');
	}


	ImageCollectionContainer.prototype.bindUIActions = function(){
		$(document).on("onElement3dLinkClick"+this.ns,this.bind(this.stopPlaying));
		$(document).on('click'+this.ns, ".js-content-close",this.bind(this.startPlaying));
		this.isEventsBinded = true;
	}

	ImageCollectionContainer.prototype.unbindUIActions = function(){
		$(document).off("onElement3dLinkClick"+this.ns);
		$(document).off('click'+this.ns);
		this.isEventsBinded = false;
	}

	ImageCollectionContainer.prototype.loadImages = function($container, $parent, className){
		var self = this;
		$container.each(function(){
			var $ele = $(this);
			var img = new Image();
			img.src = $ele.data("src");
			img.className = className;
			if (img.complete) {
				done();
			} else {
				$(img).load(done);
			}

			function done(){
				$ele.append($(img));
				self.counter--;
				if(self.counter === 0){
					self.$collectionImages = self.$imageCollection.find(".image_collection--img");
					self.numberOfImages = self.$collectionImages.length;
					if(self.isPlaying && !self.isReady){
						if (self.type == TEASER) self.render();
						self.startInterval();
					}
					self.isReady = true;
					self.isLoading = false;
				}
			}
		});
	}


	return ImageCollectionContainer;
});

/**
 * TeaserContainer.
 * @selector .js-teaser-container
 * @status enabled
*/



define (
'app/content/TeaserContainer',[
	'jquery', 'app/content/BaseModule', 'hv/animation/AnimationFrame', 'app/plugins/mediaDispatcher'
],
function(
	$, BaseModule, AnimationFrame, mediaDispatcher
) {
	var TeaserContainer;
	var ns = '.TeaserContainer'; // CHANGE THIS!
	var instanceCounter = 0;

	var TeaserContainer = function(element) {
		this.$el = null;
		this.ns = ns + (instanceCounter++);
	};

	TeaserContainer.prototype = new BaseModule();

	TeaserContainer.prototype.init = function( element ){
		var self = this;
		this.$el = $(element);
		this.initVariables();
		this.bindUIActions();
	};

	TeaserContainer.prototype.initVariables = function() {
		this.hasVideo = this.$el.find(".js-teaser-video").length > 0;
		if(this.hasVideo){
			this.video = this.$el.find(".js-teaser-video")[0];
		}
		this.$videoPoster = this.$el.find(".js-teaser-poster");
	};

	TeaserContainer.prototype.bindUIActions = function(){
		var self = this;
		this.$el.on("mouseenter"+ns, this.bind(this.mouseenterHandler));
		this.$el.on("mouseleave"+ns, this.bind(this.mouseleaveHandler));
		mediaDispatcher.isOrBelow('tablet').then(function(){
			if(self.hasVideo){
				$(self.video).removeAttr('preload');
			}
	  });
	}

	TeaserContainer.prototype.mouseenterHandler = function(event){
		var self = this;
		if(this.hasVideo){
			this.playVideo();
		}
		
		this.$el.addClass("is-active");
	}

	TeaserContainer.prototype.mouseleaveHandler = function(event){
		var self = this;
		this.$el.removeClass("is-active");
		if(this.hasVideo){
			this.stopVideo();
		}
	}

	TeaserContainer.prototype.playVideo = function(){
		this.video.play();
	}

	TeaserContainer.prototype.stopVideo = function(){
		this.video.pause();
		this.video.currentTime = 0;
	}



	return TeaserContainer;
});

/**
 * VideoCanvasContainer.
 * @selector .js-video-canvas-container
 * @status enabled
*/



define (
'app/content/VideoCanvasContainer',[
	'jquery', 'app/content/BaseModule', 'hv/animation/AnimationFrame', 'app/plugins/mediaDispatcher'
],
function(
	$, BaseModule, AnimationFrame, mediaDispatcher
) {
	var VideoCanvasContainer;
	var ns = '.VideoCanvasContainer'; // CHANGE THIS!
	var instanceCounter = 0;

	var VideoCanvasContainer = function(element) {
		this.$el = null;
		this.ns = ns + (instanceCounter++);
	};

	VideoCanvasContainer.prototype = new BaseModule();

	VideoCanvasContainer.prototype.init = function( element ){
		var self = this;
		this.$el = $(element);
		this.initVariables();
		$(document).on("world3d:currentElement"+this.ns, this.bind(this.currentElementHandler));
		mediaDispatcher.isOrBelow('tablet').then(function(){
			$(self.video).removeAttr("preload");
			self.stopVideo();
	  });
		this.prerender();
	};

	VideoCanvasContainer.prototype.initVariables = function() {
		this.video = this.$el.find(".element3dvideo")[0];
		this.maskImage = this.$el.find(".element3dmaskimage")[0];
		this.posterImage = this.$el.find(".element3dvideoposter")[0];
		this.canvas = this.$el.find(".element3dcanvas")[0];

		this.ctx = this.canvas.getContext('2d');
		this.animationFrame = false;
		this.ticking = false;
		this.isHovered = false; 
		this.closeTimer = null;
		this.isEventsBinded = false;
		this.isFirst = true;
		this.$parent = this.$el.parents(".element3dcont");
		this.level = this.$parent.data('level');
		this.index = this.$parent.index();
		this.isActive = false;
		this.isPlaying = false;
	};

	VideoCanvasContainer.prototype.prerender = function(){
		this.ctx.save();
		this.ctx.drawImage(this.posterImage, 0,0, 544,306);
		this.ctx.globalCompositeOperation = 'destination-in';
		this.ctx.drawImage(this.maskImage, 0, 0);
		this.ctx.restore();
	}

	VideoCanvasContainer.prototype.currentElementHandler = function(e,data){
		if(this.level == data.level && this.index == data.index && data.visible){
			this.isActive = true;
			if(!this.isEventsBinded){
				this.bindUIActions();
			}
			this.playVideo();
		}else{
			this.isActive = false;
			if(this.isEventsBinded){
				this.unbindUIActions();
			}
			this.stopVideo();
		}
	}

	VideoCanvasContainer.prototype.playVideo = function(){
		if(this.isPlaying) return;
		this.$el.addClass("is-active");
		this.isPlaying = true;
		this.video.play();
		this.requestEF();
	}


	VideoCanvasContainer.prototype.bindUIActions = function(){
		var self = this;
		// this.$el.on('mouseover'+this.ns,  function(){
		// 	clearTimeout(self.closeTimer);
		// 	self.$el.addClass("is-hovered");
		// 	self.isHovered = true;
		// });
		// this.$el.on('mouseout'+this.ns, function(event){
		// 	self.closeTimer = setTimeout(function(){
		// 		self.$el.removeClass("is-hovered");
		// 		self.isHovered = false;
		// 	},100);
		// });
		$(document).on("onElement3dLinkClick"+this.ns,this.bind(this.stopVideo));
		$(document).on('click'+this.ns, ".js-content-close",this.bind(this.playVideo));
		this.isEventsBinded = true;
	}

	VideoCanvasContainer.prototype.inTarget = function(eleArr,eventTarget){		  
			for (var i = 0; i < eleArr.length; i++) {
				if($.contains( eleArr[i], eventTarget ) || eleArr[i] == eventTarget){
					return true;
				}
			}
			return false;
	};

	VideoCanvasContainer.prototype.render = function(){
		this.ctx.save();
		this.ctx.drawImage(this.video, 0, 0, 544,306);
		// if(this.isHovered){
		// 	this.ctx.fillStyle = 'rgba(0,0,0,0.2)';
		// 	this.ctx.fillRect(0,0,544,306);
		// }
		this.ctx.globalCompositeOperation = 'destination-in';
		this.ctx.drawImage(this.maskImage, 0, 0);
		this.ctx.restore();
		this.ticking = false;
		this.requestEF();
	}

	VideoCanvasContainer.prototype.requestEF = function(){
		if ( !this.ticking ) {
			this.animationFrame = AnimationFrame.request(this.bind(this.render));
			this.ticking = true;
		} 
	}

	VideoCanvasContainer.prototype.cancelEF = function(){
		AnimationFrame.cancel(this.animationFrame);
		this.animationFrame = false;
		this.ticking = false;
	}

	VideoCanvasContainer.prototype.stopVideo = function(){
		if(!this.isPlaying) return;
		this.$el.removeClass("is-active");
		this.video.pause();
		this.cancelEF();
		this.isPlaying = false;
	}

	VideoCanvasContainer.prototype.unbindUIActions = function(){
		$(document).off("onElement3dLinkClick"+this.ns);
		$(document).off('click'+this.ns);
		this.isEventsBinded = false;
	}


	return VideoCanvasContainer;
});

/**
 * VideoHoverCanvasContainer.
 * @selector .js-video-hover-canvas-container
 * @status enabled
*/



define (
'app/content/VideoHoverCanvasContainer',[
	'jquery', 'app/content/BaseModule', 'hv/animation/AnimationFrame', 'app/plugins/mediaDispatcher'
],
function(
	$, BaseModule, AnimationFrame, mediaDispatcher
) {
	var VideoHoverCanvasContainer;
	var ns = '.VideoHoverCanvasContainer'; // CHANGE THIS!
	var instanceCounter = 0;

	var VideoHoverCanvasContainer = function(element) {
		this.$el = null;
		this.ns = ns + (instanceCounter++);
	};

	VideoHoverCanvasContainer.prototype = new BaseModule();

	VideoHoverCanvasContainer.prototype.init = function( element ){
		var self = this;
		this.$el = $(element);
		this.initVariables();
		this.bindUIActions();
		this.prerender();
	};


	
	VideoHoverCanvasContainer.prototype.initVariables = function() {
		this.video = this.$el.find(".element3dvideo")[0];
		this.maskImage = this.$el.find(".element3dmaskimage")[0];
		this.posterImage = this.$el.find(".element3dvideoposter")[0];
		this.canvas = this.$el.find(".element3dcanvas")[0];
		this.$playBtn = this.$el.find('.element3dvideoplaybtn');

		this.ctx = this.canvas.getContext('2d');
		this.animationFrame = false;
		this.ticking = false;
		this.isHovered = false; 
		this.closeTimer = null;
		this.isEventsBinded = false;
		this.isFirst = true;
		this.$parent = this.$el.parents(".element3dcont");
		this.level = this.$parent.data('level');
		this.index = this.$parent.index();
		this.isActive = false;
		this.isPlaying = false;

		// maskImage size
		this.imageWidth = 544;
		this.imageHeight = 306;
		this.leftMargin = ($(this.maskImage).width()-this.imageWidth)/2;
		this.topMargin = ($(this.maskImage).height()-this.imageHeight)/2;
	};

	VideoHoverCanvasContainer.prototype.prerender = function(){
		this.ctx.save();
		this.ctx.drawImage(this.posterImage, this.leftMargin,this.topMargin, this.imageWidth,this.imageHeight);
		this.ctx.fillStyle = 'rgba(0,0,0,0.2)';
		this.ctx.fillRect(this.leftMargin,this.topMargin,this.imageWidth,this.imageHeight);
		this.ctx.globalCompositeOperation = 'destination-in';
		this.ctx.drawImage(this.maskImage, 0, 0);
		this.ctx.restore();
	}

	VideoHoverCanvasContainer.prototype.playVideo = function(){
		if(this.isPlaying) return;
		this.$el.addClass("is-active");
		this.isPlaying = true;
		this.video.play();
		this.requestEF();
	}


	VideoHoverCanvasContainer.prototype.bindUIActions = function(){
		var self = this;
		mediaDispatcher.isOrBelow('tablet').then(function(){
			$(self.video).removeAttr("preload");
			self.stopVideo();
	  });
		this.$el.on('mouseover'+this.ns,  function(){
			clearTimeout(self.closeTimer);
			self.$el.addClass("is-hovered");
			self.isHovered = true;
			self.playVideo();
		});
		this.$el.on('mouseout'+this.ns, function(event){
			self.closeTimer = setTimeout(function(){
				self.$el.removeClass("is-hovered");
				self.isHovered = false;
				self.stopVideo();
			},100);
		});
		$(document).on("onElement3dLinkClick"+this.ns,this.bind(this.stopVideo));
		$(document).on('click'+this.ns, ".js-content-close",this.bind(this.playVideo));
		this.isEventsBinded = true;
	}

	VideoHoverCanvasContainer.prototype.inTarget = function(eleArr,eventTarget){		  
			for (var i = 0; i < eleArr.length; i++) {
				if($.contains( eleArr[i], eventTarget ) || eleArr[i] == eventTarget){
					return true;
				}
			}
			return false;
	};

	VideoHoverCanvasContainer.prototype.render = function(){
		this.ctx.save();
		this.ctx.drawImage(this.video, this.leftMargin, this.topMargin, this.imageWidth,this.imageHeight);
		this.ctx.globalCompositeOperation = 'destination-in';
		this.ctx.drawImage(this.maskImage, 0, 0);
		this.ctx.restore();
		this.ticking = false;
		this.requestEF();
	}

	VideoHoverCanvasContainer.prototype.requestEF = function(){
		if ( !this.ticking ) {
			this.animationFrame = AnimationFrame.request(this.bind(this.render));
			this.ticking = true;
		} 
	}

	VideoHoverCanvasContainer.prototype.cancelEF = function(){
		AnimationFrame.cancel(this.animationFrame);
		this.animationFrame = false;
		this.ticking = false;
	}

	VideoHoverCanvasContainer.prototype.stopVideo = function(){
		if(!this.isPlaying) return;
		this.$el.removeClass("is-active");
		this.video.pause();
		this.video.currentTime = 0;
		this.cancelEF();
		this.isPlaying = false;
		this.prerender();
	}


	return VideoHoverCanvasContainer;
});

define (
'app/modules/GATracker',[
	'jquery'
],
function(
	$
) {
	var ns = '.google-analytics';


	function GATracker() {
		this.initEventTracking();
		this.trackExternalLinks();
	}

	GATracker.prototype.removeParametersFromURL = function(url){
		var oldURL = url;
		var index = 0;
		var newURL = oldURL;
		index = oldURL.indexOf('?');
		if(index === -1){
		    index = oldURL.indexOf('#');
		} else {
		    newURL = oldURL.substring(0, index);
		}
		return newURL;
	};

	GATracker.prototype.track = function() {
		var args = [];
		for (var i = 0; i < arguments.length; i++) {
			args.push(arguments[i]);
		}

		if (window.ga) {
			console.log.apply(console, ['GA:'].concat(args));
			window.ga.apply(window.ga, args);
		} else {
			console.log.apply(console, ['GA (disabled):'].concat(args));
		}
	};





	GATracker.prototype.initEventTracking = function() {
		var self = this;
		var track = this.track;

		var $body = $('body');

		var trackGlobalEvent = function(type) {
			$body.on(type + ns, function(e, param){
				self.trackEvent(type, param);
			});
		};


		/* Hamburgernavigation */

		trackGlobalEvent('wos-navigation-toggle-click');

		trackGlobalEvent('wos-navigation-link-click');



		/* Dots Navigation */

		trackGlobalEvent('wos-dots-nav-el-click');

		

		/* Content */

		trackGlobalEvent('wos-detail-close-click');

		$body.on('click'+ns, '.share-video__list__item__link, .sharebox__list__link', function(e) {
			var href = $(e.currentTarget).attr('href');
			var domain = href.match(/([a-z]+)\.com\//)[1];
			track('send', 'event', 'share:' + domain, 'click', document.location.toString());
		});



		/* Hotspots */

		$body.on('wos-slideshow-hotspot-open'+ns + ' ' + 'wos-film-hotspot-open'+ns, function(e) {
			var $hotspot = $(e.target);
			var hotspotID = $hotspot.attr('id') || $hotspot.attr('href');
			if (hotspotID) {
				hotspotID = hotspotID.split('js-')[1];
			}
			self.trackEvent('wos-slideshow-hotspot-open', hotspotID);
		});



		/* Related Videos */

		$body.on('click'+ns, '.related-media__list__item__img_wrapper > a', function(e) {
			var href = $(e.target).closest('a').attr('href');
			track('send', 'related-video', 'click', href, 1);
		});

		

		/* Slideshows */

		trackGlobalEvent('wos-routenetwork-link-click');




		/* Film */

		trackGlobalEvent('wos-film-play-click');
		trackGlobalEvent('wos-film-pause-click');
		trackGlobalEvent('wos-film-mute-click');
		trackGlobalEvent('wos-film-unmute-click');



		/* Route Network */

		$body.on('click'+ns, '.iconplane .icon', function(e) {
			track('send', 'event', {
				'eventCategory': 'Routenetwork',
				'eventAction': 'click',
				'eventLabel': 'Opened Flight'
			});
		});

		$body.on('click'+ns, '.iconplane .tooltiplink.internal', function(e) {
			track('send', 'event', {
				'eventCategory': 'Routenetwork',
				'eventAction': 'click',
				'eventLabel': 'Route Network flight internal link clicked'
			});
		});
		$body.on('click'+ns, '.iconplane .tooltiplink.external', function(e) {
			track('send', 'event', {
				'eventCategory': 'Routenetwork',
				'eventAction': 'click',
				'eventLabel': 'Route Network flight external (Booking) link clicked'
			});
		});

		$body.on('click'+ns, '.iconplane .tooltip .closebutton', function(e) {
			track('send', 'event', {
				'eventCategory': 'Routenetwork',
				'eventAction': 'close tooltip',
				'eventLabel': 'Route Network flight tooltip close'
			});
		});


		$body.on('click'+ns, '.airport .icon', function(e) {
			track('send', 'event', {
				'eventCategory': 'Routenetwork',
				'eventAction': 'click',
				'eventLabel': 'Opened Destination'
			});
		});

		$body.on('click'+ns, '.airport .tooltiplink.external', function(e) {
			track('send', 'event', {
				'eventCategory': 'Routenetwork',
				'eventAction': 'click',
				'eventLabel': 'Route Network airport external link clicked'
			});
		});

		$body.on('click'+ns, '.airport .tooltip .closebutton', function(e) {
			track('send', 'event', {
				'eventCategory': 'Routenetwork',
				'eventAction': 'close tooltip',
				'eventLabel': 'Route Network airport tooltip close'
			});
		});
	};















	GATracker.prototype.trackEvent = function(event, param) {
		var self = this;
		var track = this.track;

		switch (event) {

			case 'wos-navigation-toggle-click':
				track('send', 'event', {
					'eventCategory': 'Hamburgernavigation',
					'eventAction': 'click',
					'eventLabel': param ? 'Closing hamburgernavigation' : 'Opening hamburgernavigation'
				});
				break;

			case 'wos-navigation-link-click':
				(function(href){
					var afterHash = href.substring(href.indexOf('#')+1);
					afterHash = self.removeParametersFromURL(afterHash);
					track('send', 'event', 'nav:main', 'click', afterHash, 1);
				})(param);
				break;




			/* Dots Navigation */

			case 'wos-dots-nav-el-click':
				track('send', 'event', 'nav:dot', 'click', param, 1);
				break;

			


			/* Content */

			case 'wos-detail-close-click':
				track('send', 'event', {
					'eventCategory': 'Content',
					'eventAction': 'close',
					'eventLabel': 'Closing ' + window.location.toString()
				});
				break;

			


			/* Hotspots */



			case 'wos-slideshow-hotspot-open':
			case 'wos-film-hotspot-open':
				(function(hotspotID){
					if (hotspotID) {
						var href = window.location.href+'/'+hotspotID;
						track('send', 'event', 'hotspot', 'click', href, 1);
					}
				})(param);
				break;


			


			/* Slideshows */

			case 'wos-routenetwork-link-click':
				track('send', 'event', {
					'eventCategory': 'Slideshow',
					'eventAction': 'click',
					'eventLabel': 'Link to Route Network clicked (Airplane Slideshow)'
				});
				break;



			


			/* Film */

			case 'wos-film-play-click':
				track('send', 'event', {
					'eventCategory': 'Film',
					'eventAction': 'play',
					'eventLabel': 'Played Film with button'
				});
				break;

			case 'wos-film-pause-click':
				track('send', 'event', {
					'eventCategory': 'Film',
					'eventAction': 'pause',
					'eventLabel': 'Paused Film with button'
				});
				break;

			case 'wos-film-mute-click':
				track('send', 'event', {
					'eventCategory': 'Film',
					'eventAction': 'mute'
				});
				break;

			case 'wos-film-unmute-click':
				track('send', 'event', {
					'eventCategory': 'Film',
					'eventAction': 'unmute'
				});
				break;

		}
		

	};



	GATracker.prototype.trackExternalLinks = function() {
		var ns = '.externalLinks';
		var $doc = $(document);
		var me = this;

		document.addEventListener('click', handleFirstClick, true);

		function handleFirstClick(event) {
			// too register for a click when the click has happend
			// makes sure that the event handler will be called at the end
			// -- we need that to be able to check wether the event has been default prevented already.
			$doc.off(ns);
			$doc.on('click'+ns, 'a[href]', handleSecondClick);
		}

		function handleSecondClick(event) {
			var $target = $(event.currentTarget);
			var href = $target.attr('href');
			var windowTarget = $target.attr('target');
			var localHost = window.location.host;

			if (event.isDefaultPrevented()) {
				return;
			}


			if (href.indexOf('http://') === 0 || href.indexOf('https://') === 0) {
				if (href.indexOf(window.location.origin) === 0) {
					return;
				}

				var options = {};

				// to track external links that will replace this document
				// we need to wait for the tracking hit to have taken place
				// before changing the location
				if (window.ga && (!windowTarget || windowTarget === '_self')) {
					event.preventDefault();
					options = {
						'hitCallback': function() {
							document.location = href;
						}
					};
				}
				me.track('send', 'event', 'outbound', 'click', href, options);
			}
		}
	};


	GATracker.prototype.replaceLocation = function(url, category, justReplace) {
		if (url.charAt(0) === '#') {
			url = window.location.toString().split('#')[0] + url;
		}

		// History prev
		if ( history.pushState ) {
			if (true || justReplace) {
				history.replaceState(null, category, url);
			} else {
				history.pushState(null, category, url);
			}
		} else {
			window.location.replace(url);
		}

		// we want at least 200 ms between tracking pages (otherwise it's probably the same page, just a slide)
		if (!this.lastLocationTrack || (new Date() - this.lastLocationTrack) > 200) {
			this.track('send', 'pageview', document.location.toString());
			this.lastLocationTrack = new Date();
		}
	};

	GATracker.prototype.destroy = function() {
		$(document).off(ns);
		$(window).off(ns);
	};

	return new GATracker();
});

/**
 * ImageCanvasContainer.
 * @selector .js-overlay-container
 * @status enabled
*/

define (
'app/content/ContentOverlayManager',[
	'jquery',
	'app/Config',
	'app/modules/GATracker'
],
function(
	$,
	Config,
	GATracker
) {

	var instances = 0;

	function ContentOverlayManager() {
		this.ns = ".ContentOverlayManager" + instances;
	}

	ContentOverlayManager.prototype.init = function(root) {
		this.$el = $(root || document.body);

		var overlayURLHash = this.overlayURLHash = {};
		this.getOverlayElements().each(function(){
			var $overlay = $(this);
			var url = $overlay.data('url');
			if (url) {
				overlayURLHash[url] = $overlay.attr('id');
			}
		});

		this.$el.on('click', '.js-overlay-container--close', function(event){
			event.preventDefault();
			this.hide();
		}.bind(this));


		$(document).on('click' + this.ns, 'a[href]', function(event){
			var href = $(event.currentTarget).attr('href');
			try {
				if (this.overlayURLHash[href]) {
					href = '#' + this.overlayURLHash[href];
				}
				if (href.charAt(0) === '#') {
					var $found = this.getOverlayElements().filter(href);
					if ($found.length === 1) {
						event.preventDefault();
						this.show(href.substr(1));
					}
				}
			}
			catch(e){}
		}.bind(this));


		$(document).on('keydown' + this.ns, function(event){
			if(event.keyCode === 27 && this.visible) { // ESCAPE
				this.hide();
				event.stopPropagation();
			}
		}.bind(this));
	};

	ContentOverlayManager.prototype.destroy = function() {
		$(document).off(this.ns);
	};

	ContentOverlayManager.prototype.show = function(id) {
		var $all = this.getOverlayElements();
		var $overlay = $all.filter('#' + id);
		var $current = $all.filter('is-active');

		if ($overlay.is($current)) {
			return;
		}

		this.hide();
		$overlay.addClass('is-active-new');

		if ($overlay.data('url')) {
			this.recentLocation = location.href;
			GATracker.replaceLocation($overlay.data('url'), 'overlay');
		}

		setTimeout(function(){
			$overlay.find('.js-overlay-container--close').focus();
			$overlay.removeClass('is-active-new').addClass('is-active');
		}, 30);

		this.visible = true;
	};

	ContentOverlayManager.prototype.hide = function() {
		var $all = this.getOverlayElements();
		var $current = $all.filter('.is-active');
		$current.removeClass('is-active is-active-new').addClass('was-active');

		if (this.recentLocation) {
			GATracker.replaceLocation(this.recentLocation, 'overlay');
			this.recentLocation = null;
		}

		clearTimeout(this.cleanAfterHideTimeout);
		this.cleanAfterHideTimeout = setTimeout(function(){
			$all.filter('.was-active').removeClass('was-active');
		}, 1000);

		this.visible = false;
	};

	ContentOverlayManager.prototype.getOverlayElements = function() {
		return this.$el.find('.js-content_overlay');
	};


	return ContentOverlayManager;
});

// Template for a typical site module

/*
BaseModule
 ---
Description of the main functionality/purpose of the javascript
implementation of this module in a very few words.

e.g. Makes sure of touch interactivity.
*/


define(
'app/modules/BaseModule',[
	'jquery'
],
function(
	$
){

	var BaseModule;
	var namespaces = {};

	BaseModule = function(){
		this.$el = null;
	};

	BaseModule.ns = function(name) {
		if (!namespaces[name]) {
			namespaces[name] = 0;
		}
		return '.' + name + (++namespaces[name]);
	};

	BaseModule.prototype.init = function(element){
		this.$el = $(element);
		return this;
	};

	BaseModule.prototype.destroy = BaseModule.prototype._destroy = function(){
		this.off();
		if (this.$el) {
			// remove event listeners
			this.$el = null;
		}
	};

	// on(event, selector, handler)
	// on(element, event, selector, handler)
	// on(event, handler)
	// on(element, event, handler)
	BaseModule.prototype.on = function(){
		var event, selector, handler, target, args = [];
		for (var i = 0; i < arguments.length; i++) args[i] = arguments[i];
		switch (arguments.length) {
			case 2:
				target = this.$el;
				event = args.shift();
				handler = args.shift();
				break;
			case 3:
				event = args.shift();
				if (typeof(event) === 'string') {
					target = this.$el;
					selector = args.shift();
					handler = args.shift();
				} else {
					target = $(event);
					event = args.shift();
					handler = args.shift();
				}
				break;
			case 4:
				target = $(args.shift());
				event = args.shift();
				selector = args.shift();
				handler = args.shift();
				break;
		}

		handler = this.bind(handler);

		if (selector) {
			target.on(event + this.ns, selector, handler);
		} else {
			target.on(event + this.ns, handler);
		}
	};

	BaseModule.prototype.off = function(){
		if (this.$el) this.$el.off(this.ns);
		$(document).off(this.ns);
		$(window).off(this.ns);
		if (this.nstemp) {
			if (this.$el) this.$el.off(this.nstemp);
			$(document).off(this.nstemp);
			$(window).off(this.nstemp);
		}
	};

	BaseModule.prototype.bind = function(method) {
		var self = this;
		return function(){
			method.apply(self, arguments);
		};
	};

	return BaseModule;

});

/**
 * Sharebox.
 * @selector .js-share-button
 * @status enabled
*/

define (
'app/content/Sharebox',[
	'jquery',
	'app/modules/BaseModule'
],
function(
	$, BaseModule
) {

	function Sharebox() {
		this.ns = BaseModule.ns('Sharebox');
	}

	Sharebox.prototype.init = function(element) {
		var self = this;
		this.$el = $(element);

		this.$el.on('click' + this.ns, this.openSharebox.bind(this));
		this.getShareboxEl().on('click'+this.ns, '.js-sharebox-close', this.closeSharebox.bind(this));

		return this;
	};

	Sharebox.prototype.getShareboxEl = function() {
		return this.$el.siblings('.sharebox');
	};


	Sharebox.prototype.openSharebox = function(e) {
		var $sharebox = this.getShareboxEl(),
			$body = $(document);

		$sharebox.addClass('is-visible');
		$('html').addClass('has-infobox-open');

		setTimeout(function(){
			$body.on('click' + this.ns + 'temp', ':not(.js-sharebox__box)', this.closeSharebox.bind(this));
		}.bind(this), 0);

		$sharebox.trigger('shareboxOpen');
	};

	Sharebox.prototype.closeSharebox = function(e) {
		var $sharebox = this.getShareboxEl(),
			$body = $(document);

		$sharebox.removeClass('is-visible');
		$('html').removeClass('has-infobox-open');

		$body.off(this.ns + 'temp');

		$sharebox.trigger('shareboxClose');
	};

	Sharebox.prototype.destroy = function() {
		$(document).off(this.ns);
	};

	return Sharebox;
});

/**
 * VideoChapters.
 * @selector .js-video-chapters
 * @status enabled
*/


define(
'app/content/VideoChapters',['jquery'],
function($)
{
	var instanceCounter = 0;

	function VideoChapters() {}

	VideoChapters.prototype.init = function(element) {
		this.$el = $(element);
		this.$slide = this.$el.closest('.js-slideshow-slide');
		this.ns = '.videochapter-' + (++instanceCounter);

		var videoSelector = this.$el.data('target');
		var $video = $(videoSelector);
		this.video = $video.get(0);

		this.chapters = this.$el.find('.js-video-chapters--item').toArray().map(function(el, index){
			var $el = $(el);
			return {
				el: el,
				$el: $el,
				time: Number($el.data('time')),
				left: 0,
				width: 0,
				index: index
			};
		});

		this.measureViews();
		this.moveTo(-1000, false);
		setTimeout(function(){
			this.validate();
		}.bind(this), 10);

		$(window).on('resize' + this.ns, this.measureViews.bind(this));
		$video.on('timeupdate' + this.ns, this.validate.bind(this));

		this.$el.on('click' + this.ns, '.js-video-chapters--item', this.handleItemClick.bind(this));
		this.$el.on('click' + this.ns, '.js-video-chapters--left', this.handlePageClick.bind(this));
		this.$el.on('click' + this.ns, '.js-video-chapters--right', this.handlePageClick.bind(this));
		this.$el.on('mouseenter' + this.ns, this.preventAutomove.bind(this));
		this.$el.on('mouseleave' + this.ns, this.unpreventAutomove.bind(this));
		this.$el.on('touchstart' + this.ns, function(event){
			this.preventAutomove();
			this.unpreventAutomove(5000);
		});

		this.$slide.on('slide:hide', function(event){
			if (this.currentChapter) {
				var id = this.currentChapter.$el.data('listitem');
				var $listitem = $('#' + id);
				$listitem.addClass('is-highlighted').siblings().removeClass('is-highlighted');
				setTimeout(function(){
					$listitem.removeClass('is-highlighted');
				},1500);
			}
		}.bind(this));
	};

	VideoChapters.prototype.validate = function() {
		var videoTime = this.video.currentTime || 0;

		var chapter = this.getChapterAtTime(videoTime);
		if (this.currentChapter !== chapter) {
			if (this.currentChapter) {
				this.currentChapter.$el.removeClass('is-active');
			}
			this.currentChapter = chapter;
			if (this.currentChapter) {
				this.currentChapter.$el.addClass('is-active');
			}
			this.moveToCurrent();
		}
	};

	VideoChapters.prototype.measureViews = function() {
		this.chapters.forEach(function(item, index){
			item.width = item.$el.width();
			item.left = item.$el.position().left;
		});
		var $chapterContainer = this.$el.find('.video-chapters--list');
		this.containerWidth = $chapterContainer.width();
		this.fullWidth = $chapterContainer.get(0).scrollWidth;
	};

	VideoChapters.prototype.moveTo = function(x, withTransition) {
		var $chapterContainer = this.$el.find('.video-chapters--list');

		if (x < -100) {
			x = -100;
		} else
		if (x > (this.fullWidth + 100)) {
			x = this.fullWidth + 100;
		}
		
		this.position = x;

		var left = this.containerWidth / 2 - x;
		var duration = withTransition === true ? 5 : withTransition;
		$chapterContainer.css({
			opacity: 1,
			transform: 'translateX(' + left + 'px)',
			transition: withTransition ? 'transform ' + duration + 's ease-in-out' : ''
		});
	};

	VideoChapters.prototype.moveToCurrent = function() {
		if (!this.automovePrevented) {
			var left = this.currentChapter === null ? -100 : this.fullWidth + 100;
			if (this.currentChapter) {
				left = this.currentChapter.left + this.currentChapter.width / 2;
			}
			this.moveTo(left, true);
		}
	};

	VideoChapters.prototype.preventAutomove = function() {
		clearTimeout(this.resetAutomoveTimeout);
		this.automovePrevented = true;
	};

	VideoChapters.prototype.unpreventAutomove = function(delay) {
		clearTimeout(this.resetAutomoveTimeout);
		resetAutomoveTimeout = setTimeout(function(){
			this.automovePrevented = false;
		}.bind(this), delay || 3000);
	};

	VideoChapters.prototype.handlePageClick = function(event) {
		event.preventDefault();
		var toLeft = $(event.currentTarget).hasClass('js-video-chapters--left');
		this.moveTo(this.position + (toLeft ? -1 : 1) * this.containerWidth * 0.7, 0.5);
	};

	VideoChapters.prototype.handleItemClick = function(event) {
		event.preventDefault();
		this.automovePrevented = false;
		this.video.currentTime = Number($(event.currentTarget).data('time'));
		this.validate();
		this.automovePrevented = true;
	};

	VideoChapters.prototype.getChapterAtTime = function(value) {
		var found = false;
		for (var i = 0; i < this.chapters.length; i++) {
			if (this.chapters[i].time > value) {
				return found;
			}
			found = this.chapters[i];
		}
		return found;
	};

	VideoChapters.prototype.destroy = function() {
		$(window).off(this.ns);
		$(this.video).off(this.ns);
	};

	return VideoChapters;
});

/**
 * Zoomify.
 * @selector .js-zoomify
 * @status enabled
 */



 define (
 	'app/content/Zoomify',[
 	'jquery', 'app/modules/BaseModule', 'vendor/openlayer3.min'
 	],
 	function(
 		$, BaseModule, ol
 		) {
 		var Zoomify;
	var ns = '.Zoomify'; // CHANGE THIS!
	var instanceCounter = 0;
	var TILE_SIZE = 256;
	var isTouch = false;

	var Zoomify = function(element) {
		this.$el = null;
		this.ns = ns + (instanceCounter++);
	};

	Zoomify.prototype = new BaseModule();
	var _superdestroy = Zoomify.prototype.destroy;


	Zoomify.prototype.init = function( element ){
		var self = this;
		this.$el = $(element);

		var imgWidth = parseInt(this.$el.data('width'), 10);
		var imgHeight = parseInt(this.$el.data('height'), 10);
		var imgPath = this.$el.data('src');
		var minZoom = 2;
		var maxZoom = parseInt(this.$el.data('maxzoom'), 10) || Math.floor(Math.log(imgWidth / TILE_SIZE) / Math.LN2);


		var INIT_CENTER = parseCenter(this.$el.data('center')) || [imgWidth/2, -imgHeight/2];
		var ZOOM_CENTER = parseCenter(this.$el.data('zoomcenter')) || INIT_CENTER;





		// png extra
		
		var tierSizeInTiles = [];
		var tileSize = TILE_SIZE;

		while (imgWidth > tileSize || imgHeight > tileSize) {
			tierSizeInTiles.push([
				Math.ceil(imgWidth / tileSize),
				Math.ceil(imgHeight / tileSize)
				]);
			tileSize += tileSize;
		}
		tierSizeInTiles.push([1, 1]);
		tierSizeInTiles.reverse();

		var resolutions = [1];
		var tileCountUpToTier = [0];
		var i, ii;
		for (i = 1, ii = tierSizeInTiles.length; i < ii; i++) {
			resolutions.push(1 << i);
			tileCountUpToTier.push(
				tierSizeInTiles[i - 1][0] * tierSizeInTiles[i - 1][1] +
				tileCountUpToTier[i - 1]
				);
		}


		function tileUrlFunction(tileCoord, pixelRatio, projection) {
			if (!tileCoord) {
				return undefined;
			} else {
				var tileCoordZ = tileCoord[0];
				var tileCoordX = tileCoord[1];
				var tileCoordY = -tileCoord[2] - 1;
				var tileIndex =
				tileCoordX +
				tileCoordY * tierSizeInTiles[tileCoordZ][0] +
				tileCountUpToTier[tileCoordZ];
				var tileGroup = (tileIndex / TILE_SIZE) | 0;
				return imgPath + 'TileGroup' + tileGroup + '/' +
				tileCoordZ + '-' + tileCoordX + '-' + tileCoordY + '.png';
			}
		}







		var bestZoom = Math.min(maxZoom, Math.log(this.$el.width() / TILE_SIZE) / Math.LN2);
		minZoom = Math.floor(bestZoom);

		// Maps always need a projection, but Zoomify layers are not geo-referenced, and
		// are only measured in pixels.  So, we create a fake projection that the map
		// can use to properly display the layer.
		var proj = new ol.proj.Projection({
			code: 'ZOOMIFY',
			units: 'pixels',
			extent: [0, 0, imgWidth, imgHeight]
		});

		var source = new ol.source.Zoomify({
			url: imgPath,
			size: [imgWidth, imgHeight],
			crossOrigin: 'anonymous'
		});
		source.setTileUrlFunction(tileUrlFunction);

		var view = new ol.View({
			projection: proj,
			center: INIT_CENTER,
			zoom: minZoom,
			minZoom: minZoom,
			maxZoom: maxZoom,
		    // constrain the center: center cannot be set outside
		    // this extent
		    // extent: [imgWidth * .3, -imgHeight * .7, imgWidth * .7, -imgHeight * .3]
		    extent: [0, -imgHeight, imgWidth, 0]
		});

		var map = this.map = new ol.Map({
			layers: [
			new ol.layer.Tile({
				source: source
			})
			],
			interactions: ol.interaction.defaults({
				mouseWheelZoom: false,
				pinchRotate: false
			}),
			target: this.$el.find('.js-zoomify--image').get(0) || this.$el.get(0),
			view: view
		});


		function disableButton(el, value) {
			var $el = self.$el.find(el);
			if (value) {
				$el.addClass('is-disabled');
			} else {
				$el.removeClass('is-disabled');
			}
		}

		map.on('moveend', function(event){
			validateZoom(view.getZoom());
		});



		this.on('click', '.js-zoomify--zoomin', function(event){
			event.preventDefault();
			if (isTouch) {
				zoomTo(maxZoom, ZOOM_CENTER);
			} else {
				if (view.getZoom() <= minZoom) {
					zoomTo(view.getZoom() + 1, ZOOM_CENTER);
				} else {
					zoom(+1);			
				}
			}
		});

		this.on('click', '.js-zoomify--zoomout', function(event){
			event.preventDefault();
			if (isTouch) {
				zoomTo(minZoom);
			} else {
				zoom(-1);			
			}
		});

		this.$el.closest('.js-slideshow-slide').on('slide:hide', function() {
			zoomTo(minZoom);
		});

		this.$el.closest('.js-slideshow-slide').on('slide:show', function() {
			map.updateSize();
		});

		this.on(document, 'touchstart pointerdown MSPointerDown', function(event){
			var originalEvent = event.originalEvent;
			if (originalEvent.type === 'touchstart' || originalEvent.pointerType !== 'mouse') {
				isTouch = true;
			}
		}.bind(this));


		function zoom(diff) {
			var zoom = map.getView().getZoom() + diff;
			zoomTo(zoom);
		}
		function zoomTo(zoom, center) {
			var zoomAnimation = ol.animation.zoom({
				duration: 600,
				easing: easeOutQuart,
				resolution: map.getView().getResolution()
			});
			var pan = ol.animation.pan({
				duration: 600,
				easing: easeOutQuint,
				source: view.getCenter()
			});
			if (!center && zoom <= minZoom) {
				center = INIT_CENTER;
			}

			map.beforeRender(zoomAnimation, pan);
			map.getView().setZoom(zoom);
			if (center) {
				map.getView().setCenter(center);
			}

			validateZoom(zoom);
		}

		function validateZoom(zoom) {
			zoom = Math.max(Math.min(zoom, maxZoom), minZoom);

			disableButton('.js-zoomify--zoomout', zoom <= minZoom);
			disableButton('.js-zoomify--zoomin', zoom >= maxZoom);

			var $container = self.$el.closest('.js-content-container');
			if (zoom > minZoom) {
				self.$el.addClass('is-active');
				$container.addClass('is-zoomify-active');
				if (isTouch) {
					self.$el.closest('.js-slideshow').addClass('is-scroll-disabled');
				}
			} else {
				self.$el.removeClass('is-active');
				$container.removeClass('is-zoomify-active');
				self.$el.closest('.js-slideshow').removeClass('is-scroll-disabled');
			}
		}


		validateZoom();

		// if (!window.zoomify) {
		// 	window.zoomify = [];
		// }
		// window.zoomify.push(map);

	};


	Zoomify.prototype.destroy = function() {
		if (this.map) {
			this.map.setTarget(null);
		}
		_superdestroy.call(this);
	};

	function parseCenter(value) {
		var result = false;
		if (value) {
			result = value.split(/,\s*/);
			result = [Number(result[0]), -Number(result[1])]
		}
		return result;
	}

	
	function easeOutQuint(t) {
		t--;
		return t*t*t*t*t + 1;
	}
	function easeOutQuart(t) {
		t--;
		return -t*t*t*t + 1;
	}


	return Zoomify;
});

/*
Module
 ---
Description of the main functionality/purpose of the javascript
implementation of this module in a very few words.

e.g. Makes sure of touch interactivity.
*/


define(
'app/ctxmodules/BaseModule',[
	'jquery'
],
function(
	$
){

	var Module;
	var ns = '.module-module'; // CHANGE THIS!
	var instanceCounter = 0;

	Module = function(){
		this.$el = null;
		this.ns = ns + (instanceCounter++);
	};

	Module.prototype.init = function( element ){
		this.$el = $(element);
		return this;
	};

	Module.prototype.destroy = Module.prototype._destroy = function(){
		if ( this.$el ) {
			// remove event listeners
			this.$el.off(this.ns);
			$(document).off(this.ns);
			$(window).off(this.ns);
			this.$el = null;
		}
	};

	// on(event, selector, handler)
	// on(element, event, selector, handler)
	// on(event, handler)
	// on(element, event, handler)
	Module.prototype.on = function(){
		var event, selector, handler, target, args = [];
		for (var i=0; i<arguments.length; i++) args[i] = arguments[i];
		switch ( arguments.length ) {
			case 2:
				target = this.$el;
				event = args.shift();
				handler = args.shift();
				break;
			case 3:
				event = args.shift();
				if ( typeof(event) == 'string' ) {
					target = this.$el;
					selector = args.shift();
					handler = args.shift();
				} else {
					target = $(event);
					event = args.shift();
					handler = args.shift();
				}
				break;
			case 4:
				target = $(args.shift());
				event = args.shift();
				selector = args.shift();
				handler = args.shift();
				break;
		}
		if ( selector ) {
			target.on( event+this.ns, selector, handler );
		} else {
			target.on( event+this.ns, handler );
		}
	};

	Module.prototype.bind = function(method) {
		var self = this;
		return function(){
			method.apply(self, arguments);
		};
	};

	return Module;

});

/**
 * SameHeight - Can be used to have multiple element sync their height.
 * @selector .js-sameheight
 * @status enabled
*/




define(
'app/ctxmodules/SameHeight',[
	'jquery',
	'app/ctxmodules/BaseModule'
],
function(
	$, BaseModule
){

	var SameHeight;
	var ns = '.sameheight'; // CHANGE THIS!
	var instanceCounter = 0;

	var groups = {};


	SameHeight = function(){
		this.$el = null;
		this.ns = ns + (instanceCounter++);
	};

	SameHeight.prototype = new BaseModule();

	SameHeight.prototype.init = function( element ){
		var self = this;
		// { useHeight: true }
		this.options = $(element).data('sameheight-options') || {};
		
		var group = $(element).data('sameheight');
		if ( group ) {
			group = this.getGroup(group);
			group.add(element);
		} else {
			group = this.getGroup('group'+this.ns);
			$(element).find('.js-sameheight-item').each(function(){
				group.add(this);
			});
		}


		invalidateResize();

		return this;
	};


	SameHeight.prototype.getGroup = function(name){
		if ( !groups[name] ){
			groups[name] = new SameHeightGroup(this.options);
		}
		return groups[name];
	};

	SameHeight.prototype.destroy = function(){
		// if ( groups[group] ){
		// 	groups[group].destroy();
		// 	delete groups[group];
		// }
	};


	var resizeTimeout;
	function invalidateResize(){
		clearTimeout(resizeTimeout);
		resizeTimeout = setTimeout(validateResize,1);
	}
	function validateResize(){
		for ( var name in groups ) {
			groups[name].validate();
		}
	}
	$(window).resize(invalidateResize);


	var SameHeightGroup = function(options){
		this.elements = [];
		this.ns = ns + (instanceCounter++);
		this.enabled = true;
		this.options = options || {};
		this.property = this.options.useHeight ? 'height' : 'min-height';

	};

	SameHeightGroup.prototype.add = function( element ){
		this.elements.push(element);
	};

	SameHeightGroup.prototype.enable = function(){
		if ( !this.enabled ) {
			this.enabled = true;
			invalidateResize();
		}
	};

	SameHeightGroup.prototype.disable = function(){
		if ( this.enabled ) {
			this.enabled = false;
			invalidateResize();
		}
	};

	SameHeightGroup.prototype.destroy = function(){
		$(this.elements).css(this.property,'');
		this.elements = [];
	};

	SameHeightGroup.prototype.validate = function(){
		var $all = $(this.elements);
		$all.css(this.property,'');
		if ( this.enabled ) {
			$all.css('transition',this.property + ' 0s');
			var minHeight = 0;
			$all.each(function(){
				var height = $(this).height();
				if ( height > minHeight ) {
					minHeight = height;
				}
			});
			$all.css( this.property, minHeight);
			$all.css('transition','');
		}
	};



	return SameHeight;

});

define(
'app/modules',[
	'lib/util/contextTrigger',
	'lib/util/ModuleManager'
],
function(
	contextTrigger, ModuleManager
){

	// every module should at least implement two methods
	// Module.init = function( HTMLElement )
	// Module.destroy = function()
	//
	// Modules are per se site specific (if necessary).

	var time = new Date();


	contextTrigger.add('.js-image_collection_container', function(){
		var elem = this;
		require(['app/content/ImageCollectionContainer'], function( Module ){
			ModuleManager.connect( Module, elem );
		});
	});

	contextTrigger.add('.js-teaser-container', function(){
		var elem = this;
		require(['app/content/TeaserContainer'], function( Module ){
			ModuleManager.connect( Module, elem );
		});
	});

	contextTrigger.add('.js-video-canvas-container', function(){
		var elem = this;
		require(['app/content/VideoCanvasContainer'], function( Module ){
			ModuleManager.connect( Module, elem );
		});
	});

	contextTrigger.add('.js-video-hover-canvas-container', function(){
		var elem = this;
		require(['app/content/VideoHoverCanvasContainer'], function( Module ){
			ModuleManager.connect( Module, elem );
		});
	});

	contextTrigger.add('.js-overlay-container', function(){
		var elem = this;
		require(['app/content/ContentOverlayManager'], function( Module ){
			ModuleManager.connect( Module, elem );
		});
	});

	contextTrigger.add('.js-share-button', function(){
		var elem = this;
		require(['app/content/Sharebox'], function( Module ){
			ModuleManager.connect( Module, elem );
		});
	});

	contextTrigger.add('.js-video-chapters', function(){
		var elem = this;
		require(['app/content/VideoChapters'], function( Module ){
			ModuleManager.connect( Module, elem );
		});
	});

	contextTrigger.add('.js-zoomify', function(){
		var elem = this;
		require(['app/content/Zoomify'], function( Module ){
			ModuleManager.connect( Module, elem );
		});
	});

	contextTrigger.add('.js-sameheight', function(){
		var elem = this;
		require(['app/ctxmodules/SameHeight'], function( Module ){
			ModuleManager.connect( Module, elem );
		});
	});


	contextTrigger.validate( 'body' );

	console.log("Selecting modules took: ", new Date() - time, 'ms');

	return ModuleManager;
});

define('hv/net/HTMLLoader',["jquery"], function($){

	var STRIP_SCRIPT = /<script\b[^<]*(?:(?!<\/script>)<[^<]*)*<\/script>/gi;
	var STRIP_BODY = /<body\b[^>]*>([\s\S]*?)<\/body>/gmi;

	var defaultOptions = {
		ignoreInlineScript: false
	};


	var Loader = function( options ) {
		this.options = $.extend( {}, defaultOptions, options );
		this.loading = false;
	};

	Loader.prototype.load = function( url, complete, options ) {
		var me = this;
		//this.cancel();
		options = options || {};
		options.success = function(data) {
			me.handleSuccess(data, complete);
		};

		this.loading = true;
		this.xhr = $.ajax( url, options);
	};

	Loader.prototype.isLoading = function() {
		return this.loading;
	};

	Loader.prototype.handleSuccess = function(data, callback) {
		var $Dummy = $('<div id="#body">');
		var strBody = data;

		// if we have a body tag, let's continue to work with only that one
		if ( strBody.indexOf('<body') >= 0 ) {
			strBody = data.match(STRIP_BODY)[0];
		}

		// let's get rid of all script tags (if not otherwise in options)
		if ( !this.options.ignoreInlineScript && strBody.indexOf('<script') ) {
			strBody = strBody.replace( STRIP_SCRIPT, '' );
		}

		if (callback) callback( strBody, data );

		this.xhr = null;
		this.loading = false;
	};

	Loader.prototype.cancel = function() {
		if ( this.xhr ) {
			this.xhr.abort();
			this.xhr = null;
			this.loading = false;
		}
	};

	Loader.prototype.dispose = function() {
		this.cancel();
	};

	return Loader;


});

define(
	'app/3d/Point.class',['jquery'],
	function( $ ){


	function Point(x, y)
	{
		this.x = x || 0;
		this.y = y || 0;
	}

	Point.prototype.setPosition = function( x, y ) 
	{
		this.x = x || 0;
		this.y = y || 0;
	}

	Point.prototype.translate = function(x, y)
	{
		this.x += x;
		this.y += y;
	}

	return Point;
});

define(
	'app/3d/Point3d.class',['jquery'],
	function( $ ){


	function Point3d(x, y, z)
	{
		this.x = x || 0;
		this.y = y || 0;
		this.z = z || 0;
	}
	
	Point3d.prototype.setPosition = function( x, y, z ) 
	{
		this.x = x || 0;
		this.y = y || 0;
		this.z = z || 0;
	}
	
	Point3d.prototype.translate = function( x, y, z )
	{
		this.x += x;
		this.y += y;
		this.z += z;
	}


	return Point3d;
});

define('hv/util/MathX',['jquery', 'app/3d/Point.class'], function($, Point){


	function _getQBezierValue(t, p1, p2, p3)
	{
		var iT = 1 - t;
		return iT * iT * p1 + 2 * iT * t * p2 + t * t * p3;
	}

	var MathX = {

		range: function range( v, min, max )
		{
			return Math.max( min, Math.min(v, max) );
		},

		outsideRange: function outsideRange( v, min, max )
		{
			if( v<min || v>max )
			{
				return v;
			}
			else if( Math.abs( v-min ) < Math.abs( v-max ) )
			{
				return min;
			}
			else
			{
				return max;
			}
		},

		deCasteljau: function deCasteljau( t, p0, p1, cp0, cp1 )
		{
			var Ax = ( (1 - t) * p0.x ) + (t * cp0.x);
			var Ay = ( (1 - t) * p0.y ) + (t * cp0.y);
			var Bx = ( (1 - t) * cp0.x ) + (t * cp1.x);
			var By = ( (1 - t) * cp0.y ) + (t * cp1.y);
			var Cx = ( (1 - t) * cp1.x ) + (t * p1.x);
			var Cy = ( (1 - t) * cp1.y ) + (t * p1.y);

			var Dx = ( (1 - t) * Ax ) + (t * Bx);
			var Dy = ( (1 - t) * Ay ) + (t * By);

			var Ex = ( (1 - t) * Bx ) + (t * Cx);
			var Ey = ( (1 - t) * By ) + (t * Cy);

			var Px = ( (1 - t) * Dx ) + (t * Ex);
			var Py = ( (1 - t) * Dy ) + (t * Ey);

			return new Point( Px, Py );
		},

		currentPoint: function currentPoint( t, p0, p1, p2, p3 )
		{
			var cube = t * t * t;
			var square = t * t;
			var ax = 3 * (p1.x - p0.x);
			var ay = 3 * (p1.y - p0.y);
			var bx = 3 * (p2.x - p1.x) - ax;
			var by = 3 * (p2.y - p1.y) - ay;
			var cx = p3.x - p0.x - ax - bx;
			var cy = p3.y - p0.y - ay - by;
			var x = (cx * cube) + (bx * square) + (ax * t) + p0.x;
			var y = (cy * cube) + (by * square) + (ay * t) + p0.y;
			return new Point(x, y);
		},

		getQuadraticCurvePoint: function getQuadraticCurvePoint( t, p0, p1, cp0) {
			return new Point( _getQBezierValue(t, p0.x, cp0.x, p1.x), _getQBezierValue(t, p0.y, cp0.y, p1.y ) );
		},

		distance: function distance( p1, p2 ) {
			var xs = p1.x - p2.x;
			var ys = p1.y - p2.y;
			return Math.sqrt( xs*xs + ys*ys );
		},

		distance3d: function distance3d( p1, p2 ) {
			var xs = p1.x - p2.x;
			var ys = p1.y - p2.y;
			var zs = p1.z - p2.z;
			return Math.sqrt( xs*xs + ys*ys + zs*zs );
		},

		cubicN: function cubicN(T, a,b,c,d) {
		    var t2 = T*T;
		    var t3 = t2*T;
		    return a + (-a * 3 + T * (3 * a - a * T)) * T
		    + (3 * b + T * (-6 * b + b * 3 * T)) * T
		    + (c * 3 - c * 3 * T) * t2
		    + d * t3;
		},

		getCubicBezierXYatT: function getCubicBezierXYatT(T, startPt, endPt, controlPt1, controlPt2){
		    var x=MathX.cubicN(T,startPt.x,controlPt1.x,controlPt2.x,endPt.x);
		    var y=MathX.cubicN(T,startPt.y,controlPt1.y,controlPt2.y,endPt.y);
			return new Point(x, y);
		},


		//
		// bezier intersection
		//
		sgn: function sgn( x )
		{
		    if (x < 0.0) return -1;
		    return 1;
		},

		sortSpecial: function sortSpecial(a)
		{
		    var flip;
		    var temp;

		    do {
		        flip=false;
		        for (var i=0;i<a.length-1;i++)
		        {
		            if ((a[i+1]>=0 && a[i]>a[i+1]) ||
		                (a[i]<0 && a[i+1]>=0))
		            {
		                flip=true;
		                temp=a[i];
		                a[i]=a[i+1];
		                a[i+1]=temp;

		            }
		        }
		    } while (flip);
			return a;
		},

		cubicRoots: function cubicRoots(P)
		{
		    var a=P[0];
		    var b=P[1];
		    var c=P[2];
		    var d=P[3];

		    var A=b/a;
		    var B=c/a;
		    var C=d/a;

		    var Q, R, D, S, T, Im;

		    var Q = (3*B - Math.pow(A, 2))/9;
		    var R = (9*A*B - 27*C - 2*Math.pow(A, 3))/54;
		    var D = Math.pow(Q, 3) + Math.pow(R, 2);    // polynomial discriminant

		    var t=Array();

		    if (D >= 0)                                 // complex or duplicate roots
		    {
		        var S = MathX.sgn(R + Math.sqrt(D))*Math.pow(Math.abs(R + Math.sqrt(D)),(1/3));
		        var T = MathX.sgn(R - Math.sqrt(D))*Math.pow(Math.abs(R - Math.sqrt(D)),(1/3));

		        t[0] = -A/3 + (S + T);                    // real root
		        t[1] = -A/3 - (S + T)/2;                  // real part of complex root
		        t[2] = -A/3 - (S + T)/2;                  // real part of complex root
		        Im = Math.abs(Math.sqrt(3)*(S - T)/2);    // complex part of root pair

		        /*discard complex roots*/
		        if (Im!=0)
		        {
		            t[1]=-1;
		            t[2]=-1;
		        }

		    }
		    else                                          // distinct real roots
		    {
		        var th = Math.acos(R/Math.sqrt(-Math.pow(Q, 3)));

		        t[0] = 2*Math.sqrt(-Q)*Math.cos(th/3) - A/3;
		        t[1] = 2*Math.sqrt(-Q)*Math.cos((th + 2*Math.PI)/3) - A/3;
		        t[2] = 2*Math.sqrt(-Q)*Math.cos((th + 4*Math.PI)/3) - A/3;
		        Im = 0.0;
		    }

		    /*discard out of spec roots*/
		    for (var i=0;i<3;i++)
		        if (t[i]<0 || t[i]>1.0) t[i]=-1;

		    /*sort but place -1 at the end*/
		    t= MathX.sortSpecial(t);

		   // console.log(t[0]+" "+t[1]+" "+t[2]);
		    return t;
		},

		bezierCoeffs: function bezierCoeffs(P0,P1,P2,P3)
		{
			var Z = Array();
			Z[0] = -P0 + 3*P1 + -3*P2 + P3;
		    Z[1] = 3*P0 - 6*P1 + 3*P2;
		    Z[2] = -3*P0 + 3*P1;
		    Z[3] = P0;
			return Z;
		},


		computeIntersections: function computeIntersections(px,py,lx,ly,linP, ctx )
		{

			var isDraw = false;

		    var X=Array();

		    var A=ly[1]-ly[0];	    //A=y2-y1
		    var B=lx[0]-lx[1];	    //B=x1-x2
		    var C=lx[0]*(ly[0]-ly[1]) +
		          ly[0]*(lx[1]-lx[0]);	//C=x1*(y1-y2)+y1*(x2-x1)

		    var bx = MathX.bezierCoeffs(px[0],px[1],px[2],px[3]);
		    var by = MathX.bezierCoeffs(py[0],py[1],py[2],py[3]);

		    var P = Array();
		    P[0] = A*bx[0]+B*by[0];		/*t^3*/
		    P[1] = A*bx[1]+B*by[1];		/*t^2*/
		    P[2] = A*bx[2]+B*by[2];		/*t*/
		    P[3] = A*bx[3]+B*by[3] + C;	/*1*/

		    var r=MathX.cubicRoots(P);


		    if(isDraw)
		    {
			    ctx.strokeStyle='#00cc00';
			    ctx.lineWidth=1;
			    ctx.globalAlpha = 1;
			    ctx.moveTo( px[0], py[0] );
	    	    ctx.bezierCurveTo( px[1],py[1], px[2], py[2], px[3], py[3] );
	    	    ctx.stroke();

	    	    ctx.strokeStyle='#ff0000';
			    ctx.lineWidth=1;
			    ctx.moveTo( lx[0], ly[0])
			    ctx.lineTo( lx[1], ly[1] );

			    ctx.stroke();
			}

		    /*verify the roots are in bounds of the linear segment*/
		    var minDist = 1000000;
		    var minDistId = 0;
		    var dPoints = [];

		    for (var i=0;i<3;i++)
		    {
		        t=r[i];

		        X[0]=bx[0]*t*t*t+bx[1]*t*t+bx[2]*t+bx[3];
		        X[1]=by[0]*t*t*t+by[1]*t*t+by[2]*t+by[3];

		        /*above is intersection point assuming infinitely long line segment,
		          make sure we are also in bounds of the line*/
		        var s;
		         if ((lx[1]-lx[0])!=0)           /*if not vertical line*/
		           s=(X[0]-lx[0])/(lx[1]-lx[0]);
		        else
		            s=(X[1]-ly[0])/(ly[1]-ly[0]);

		        /*in bounds?*/
		        if (t<0 || t>1.0 || s<0 || s>1.0)
		        {
		            X[0]=-100;  /*move off screen*/
		            X[1]=-100;
		        }

		        dPoints.push({x:X[0],y:X[1]});


		    	if(isDraw)
		    	{
				    ctx.beginPath();
				    ctx.lineWidth=1;
				    ctx.rect( dPoints[i].x, dPoints[i].y, 10, 10 );
				    ctx.strokeStyle='#0000ff';
				    ctx.stroke();
				}


		       var dist = MathX.distance( linP, new Point(X[0], X[1]));
		       if( dist < minDist)
		       {
		       		minDistId = i;
		       		minDist = dist;
		       }

		       return new Point(X[0], X[1]);
		    }

			if(isDraw)
			{
				ctx.beginPath();
			    ctx.lineWidth=1;
			    ctx.rect( dPoints[minDistId].x, dPoints[minDistId].y, 10, 10 );
			    ctx.strokeStyle='#00FF00';
			    ctx.stroke();
			}


		  return new Point(dPoints[minDistId].x, dPoints[minDistId].y);
		}

	};


	return MathX;
});

define(
	'app/3d/Math3d.class',['jquery', 'app/3d/Point.class', 'app/3d/Point3d.class', 'hv/util/MathX'],
	function( $, Point, Point3d, MathX ){

	var MAX_SCALE = 40;
	var FLEN = 2000;
	var XOFFSET = 0; // to center the elements visually better - it's basically a dirty fix

	var sinAngle, cosAngle;


	function Math3d()
	{
	}


	Math3d.prototype.setCameraPos = function( p )
	{
		this.cameraPos = p;
	}


	Math3d.prototype.setCenter = function( cX, cY )
	{
		this.centerX = cX;
		this.centerY = cY;
	}

	Math3d.prototype.setWindowSize = function( w, h )
	{
		this.windowW = w;
		this.windowH = h;
	}


	Math3d.prototype.addStagePosition = function( p )
	{
		return new Point( p.x+this.centerX-(this.cameraPos.x + XOFFSET), p.y+this.centerY-this.cameraPos.y );
	}


	Math3d.prototype.setAngle = function( a )
	{
		sinAngle = Math.sin( a );
		cosAngle = Math.cos( a );
	}


	Math3d.prototype.rotate3d = function( p )
	{
		var rotX = cosAngle*p.x + sinAngle*(p.z+this.cameraPos.z+50);
		var rotZ = -sinAngle*p.x + cosAngle*(p.z+this.cameraPos.z+50);
		return new Point3d( rotX, p.y, rotZ -50);
		//return new Point3d( p.x, p.y, p.z+this.cameraPos.z );
	}


	Math3d.prototype.project = function( p )
	{
		//prevents connections glitches
		//pz = MathX.range(p.z, -20000, 4000);
		pz = p.z;

		var px = FLEN / ( FLEN - pz ) * (  p.x - (this.cameraPos.x + XOFFSET) ) + (this.cameraPos.x + XOFFSET); 
		var py =  FLEN / ( FLEN - pz ) * ( - p.y - this.cameraPos.y ) + this.cameraPos.y; 

		return new Point(px, py);
	}


	Math3d.prototype.getScale = function( pRot, p2 )
	{		
		var pRotDiffX = new Point3d( pRot.x, pRot.y, pRot.z );
		pRotDiffX.x += 100;
		var p2Diff = this.project( pRotDiffX );
		var scale = Math.abs(p2.x-p2Diff.x)/100;

		return MathX.range(scale, 0, MAX_SCALE);
	}


	Math3d.prototype.getAlpha = function( pRot, scale )
	{
		var alpha = 1;
 		if(pRot.z>600)
		{
			alpha = MathX.range((600-(pRot.z-600)*2)/500, 0, 1);
		}
		else if(pRot.z<-1500)
		{
			alpha = MathX.range((pRot.z+6000)/4500, 0, 1);
		}
		return alpha;
	}

	Math3d.prototype.getAlphaCloud = function( pRot, scale )
	{
		var alpha = 1;
		if(pRot.z>600)
		{
			alpha = MathX.range((600-(pRot.z-600)*2)/500, 0, 1);
		}
		else if(pRot.z<-4000)
		{
			alpha = MathX.range((pRot.z+7000)/3000, 0, 1);
		}
		return alpha;
	}


	return Math3d;
});

define(
	'app/3d/Camera3d.class',['jquery', 'app/3d/Point.class', 'app/3d/Point3d.class', 'hv/util/MathX' ],
	function( $, Point, Point3d, MathX ){

	var MAX_SPEED = 600;

	var MAX_DIRECT_SPEED = 2000;
	
	function Camera3d( math3d, maxZPos, context )
	{
		this.ctx = context;

		this.math3d = math3d;
		this.position = new Point3d();

		this.maxZPos = maxZPos;

		this.a = 0;
		this.tA = 0;
	
		this.tX =0, this.tY =0, this.tZ = 0;

		this.aDif = 0;
		this.xDif = 0;
		this.yDif = 0;

		this.isGoingDirectly = false;
	}


	Camera3d.prototype.countNextPos = function( ) 
	{
		var s = (this.isGoingDirectly==true)?MAX_DIRECT_SPEED:MAX_SPEED;

		var delay = 10;

		var difA = (this.tA + this.aDif - this.a)/delay;
		difA = MathX.range(difA, -.02, .02);
		
		var difX = (this.tX + this.xDif - this.position.x)/delay;
		difX = MathX.range(difX, -s, s);
		
		var difY = (this.tY + this.yDif - this.position.y)/delay;
		difY = MathX.range(difY, -s, s);
		if( this.isGoingDirectly )
			difY = MathX.range(difY, -s/10, s/10);

		// + 15000 allows to zoom closer into route network's switzerland
		// it's just a manual try'n'error value ...
		this.tZ = MathX.range(this.tZ, -4000, this.maxZPos);

		var difZ = (this.tZ - this.position.z)/10;
		difZ = MathX.range(difZ, -s, s);		
		
		this.a += difA;
		
		this.position.x += difX;
		this.position.y += difY;
		this.position.z += difZ;
		
		this.math3d.setAngle( this.a );
		this.math3d.setCameraPos( this.position );
	}

	Camera3d.prototype.setMaxZPos = function( maxZPos )
	{
		this.maxZPos = maxZPos;
	}


	Camera3d.prototype.setPosition = function( x, y, z )
	{
		this.tX = x;
		this.tY = y;
		this.tZ = z;
		this.position.x = x;
		this.position.y = y;
		this.position.z = z;		
	}


	Camera3d.prototype.move = function( x, y, z )
	{
		this.tX += x;
		this.tY += y;
		this.tZ += z;

		this.isGoingDirectly = false;
	}

	Camera3d.prototype.setTargetXY = function( x, y )
	{
		this.tX = x;
		this.tY = y;
	}

	Camera3d.prototype.setTargetZ = function( z )
	{
		this.tZ = z;
	}

	Camera3d.prototype.findCurrentCameraPos = function( p1, p2 )
	{
		//
		// Finds camera position on a straight line between two closest elements.
		//	
		var pos = (-this.position.z-p1.z)/(p2.z-p1.z);

		if ( pos < 0 ) {
			p2 = p1;
		} else {
			pos = easeQuart(pos);
		}


		var tx = (p2.x-p1.x)*pos+p1.x;
		var ty = (p2.y-p1.y)*pos+p1.y;

		if( this.isGoingDirectly == false ){
			this.setTargetXY( tx, -ty );
		}
	};


	function easeQuart(t) {
		t /= 1/2;
		if (t < 1) return 1/2*t*t;
		t -= 2;
		return -1/2 * (t*t - 2);
	}


	Camera3d.prototype.setSplinesData = function ( d )
	{
		this.splinesData = d;
	};


	Camera3d.prototype.findCurrentCameraPosBezier = function( p1, p2 )
	{

		//p = Math.min(p1, p2);

		if( p1>p2 )
		{
			tmp = p2;
			p2 = p1;
			p1 = tmp;
		}

		var d = this.splinesData[p1];

		var d0 = this.math3d.addStagePosition( this.math3d.project( this.math3d.rotate3d( d[0] ) ) );
		var d1 = this.math3d.addStagePosition( this.math3d.project( this.math3d.rotate3d( d[1] ) ) );
		var d2 = this.math3d.addStagePosition( this.math3d.project( this.math3d.rotate3d( d[2] ) ) );
		var d3 = this.math3d.addStagePosition( this.math3d.project( this.math3d.rotate3d( d[3] ) ) );


		//d1 = new Point( (d3.x-d0.x)*.5+d0.x, (d3.y-d0.y)*.5+d0.y );
		//d2 = new Point( (d3.x-d0.x)*.5+d0.x, (d3.y-d0.y)*.5+d0.y );

		var pos = (-this.position.z-d[0].z)/(d[3].z-d[0].z);

		if( p == p2 )
		{
			pos = 1-pos;
		}

		p = MathX.deCasteljau( +pos, d0, d3, d1, d2 );

		var tx = (d3.x-d0.x)*pos+d0.x;
		var ty = (d3.y-d0.y)*pos+d0.y;

		if( this.isGoingDirectly == false ){
			this.setTargetXY( d0.x, d0.y );
		}

		this.ctx.beginPath();
		this.ctx.strokeStyle = '#aaaaaa';
		this.ctx.moveTo( d0.x, d0.y );

		this.ctx.bezierCurveTo( d1.x, d1.y, d2.x, d2.y, d3.x, d3.y ); 

		this.ctx.moveTo( 0, 0 );
		this.ctx.lineTo( 100, 100 );

		this.ctx.stroke();
	};




	Camera3d.prototype.setAngle = function(a)
	{
		this.tA = a*Math.PI/180;
	}

	Camera3d.prototype.getAngle = function()
	{
		return this.tA*180/Math.PI;
	}

	
	Camera3d.prototype.setAngleDif = function(a)
	{
		//small stage left/right movement
		this.aDif = -20*a*Math.PI/180;
	}


	Camera3d.prototype.setPositionDif = function( pX, pY )
	{
		this.xDif = pX * 50;
		this.yDif = pY * 50;

		this.setAngleDif(pX/15);
	}




	return Camera3d;
});

define('app/Helpers',['jquery'], function($){

	
	var isWebkit = navigator.userAgent.match(/webkit/i);
	var isIE = navigator.userAgent.indexOf('Trident') >= 0;

	var Helpers = {

		isTouchDevice: function isTouchDevice() {
			return !!('ontouchstart' in window);
		},

		translate: function translate( elem, x, y, z, r, s, a, zindex, omit3d ) {
			
			if( a != undefined )
			{
				var isHidden = a < 0.01;

				var v = isHidden?'hidden':'visible';
				elem.style.display = !isHidden ? 'block' : 'none';
				elem.style.visibility = v;
				
				if (isHidden) {
					return;
				}
				elem.style.opacity = applyPrecision(a, 15);
			}

			if (!zindex) zindex = 0;
			if (!x) x = 0;
			if (!y) y = 0;
			if (!z) z = 0;
			if (!r) r = 0;			
			if (!s) s = 1;
			s= applyPrecision(s, 15);
			//if (!a) a = 0;
			//if (!zindex) zindex = 1;

			if( Modernizr.csstransforms3d && !omit3d && !isIE )
			{
				//todo: doesn't work in IE11

				var transform = 'translateZ('+applyPrecision(z||zindex, 15)+'px) translateX('+applyPrecision(x, 15)+'px) translateY('+applyPrecision(y, 15)+'px) scale3d('+s+','+s+','+s+')  rotateZ('+applyPrecision(r, 15)+'deg)';
				// only do 3d transforms for webkit browsers - others don't do it well, especially ff
				elem.style.webkitTransform = transform;
				elem.style.transform = transform;
			}
			else if ( Modernizr.csstransforms ) 
			{
				// we don't do rotation on IE9+ and FF because
				// - FF won't render the lines nicely
				// - IE shows render bugs (not displaying text) as of now
				$(elem).css({
					'transform': 'translate('+applyPrecision(x, 15)+'px,'+applyPrecision(y, 15)+'px) scale('+s+') rotate('+applyPrecision(r, 15)+'deg)'
				});
				elem.style.zIndex = zindex;
			}
			else
			{
				elem.style.display = ( x > 3000 || y>2000 || x<-1000 || y<-1000 )? 'none' : 'block';
				elem.style.left = Math.round(x) + 'px';
				elem.style.top = Math.round(y) + 'px';
				elem.style.zIndex = zindex;
			}

			if( a != undefined )
			{
				elem.style.opacity = applyPrecision(a, 15);
			}
			

		},
		translate2d: function translate2d( elem, x, y, z, r, s, a, zindex ) {
			this.translate( elem, x, y, z, r, s, a, zindex, true);
		},

		hide: function hide( elem ) {
			elem.style.visibility = 'hidden';
		},
		show: function show( elem ) {
			elem.style.visibility = 'visible';
		}

	}

	function applyPrecision(value, precision) {
		var factor = Math.pow(10, precision);
		return Math.round(value * factor) / factor;
	}
	

	return Helpers;
});

define(
	'app/3d/Cloud3d.class',['jquery', 'app/3d/Point3d.class', 'app/Helpers', 'app/Config'],
	function( $, Point3d, Helpers, Config ){


	var counter = 0;
	var RANDOM_CLOUDS = Config.get( 'randomClouds');


	function Cloud3d( cont, path )
	{
		this.cont = cont;
		this.path = path;
		this.position = new Point3d();
		this.createElementDiv();

		this.scale = 4 + Math.random() * 4;
		this.rotation = Math.random() * 360;
	}


	Cloud3d.prototype.setPosition = function( x, y, z ) 
	{
		this.position.setPosition( x, y, z );
	}


	Cloud3d.prototype.getPosition = function() 
	{
		return this.position;
	}


	Cloud3d.prototype.render = function( p, scale, alpha, counter )
	{
		var zindex = 0;
		//if( counter == 0 ) {
			zindex = parseInt(scale*200)+600;
		//}

		Helpers.translate( this.$text[0], p.x, p.y, zindex, 0, scale*this.scale, alpha.toFixed(7), zindex );
	}


	Cloud3d.prototype.createElementDiv = function()
	{
		var text = '<div class="cloud3dCont">';		

		var i =  Math.floor(Math.random()*RANDOM_CLOUDS.length);
		if( this.path == undefined ) this.p = RANDOM_CLOUDS[ i ];
		else this.p = this.path;

		text += '<img class="cloud3d" src="'+this.p+'">';
		text += '</div>';
		this.$text = $( text );
		this.$text.attr('id','cloud-'+(++counter));

		var duration = (Math.random() * 120 + 80) + 's';
		this.$text.children()[0].style.webkitAnimationDuration = duration;
		if ( Math.random() > 0.5  ) {
			this.$text.children()[0].style.webkitAnimationDirection = 'reverse';
		}

		this.cont.append( this.$text );
	}



	return Cloud3d;
});

define(
	'app/3d/Clouds3d.class',['jquery', 'app/3d/Cloud3d.class', 'app/Helpers'],
	function( $, Cloud3d, Helpers ){
	

	function Clouds3d( math3d )
	{
		this.clouds = [];
		this.math3d = math3d;
		this.cont = $( "#cloudscontainerid");

		this.zTaken = {};
	}


	Clouds3d.prototype.buildCloud = function( x, y, z, path )
	{
		e = new Cloud3d( this.cont, path );

		this.clouds.push( e );

		// let's make sure those clouds have a minimum z distance
		// to avoid flickering
		while ( this.zTaken[Math.floor(z/10)] ) {
			z+=10;
		}

		this.zTaken[Math.floor(z/10)] = true;

		e.setPosition( x, y, z );

		return e;
	}


	Clouds3d.prototype.render = function( counter )
	{
		var i, e, p, pRot, pRotDiffX, p2, p2Diff, scale, alpha, campos;

		for( i = 0; i < this.clouds.length; i++ )
		{
			e = this.clouds[i];
			p = e.getPosition();

			campos = this.math3d.cameraPos;

			//some looping
			
			// if( e.path == undefined ){
			// 	if( p.z + campos.z < -10000 )
			// 	{
			// 		p.z += 12000;
			// 	}
			// 	else if( p.z + campos.z >  3000 )
			// 	{
			// 		p.z -= 12000;
			// 	}
			// }


			pRot = this.math3d.rotate3d( p );
			p2 = this.math3d.project( pRot );

			scale = this.math3d.getScale( pRot, p2 );

			var alpha = this.math3d.getAlphaCloud( pRot, scale );
			
			p2 = this.math3d.addStagePosition( p2 );

			e.render( p2, scale, alpha, counter ); 
		}
	}


	return Clouds3d;
});

define(
	'app/3d/Element3d.class',['jquery', 'app/3d/Point.class', 'app/3d/Point3d.class', 'app/Helpers'],
	function( $, Point, Point3d, Helpers ){


	function Element3d( id, element )
	{
		this.id = id;
		this.element = element[0];

		this.position = new Point3d();

		this.isHidden = false;

		this.position2d = new Point();
		this.alpha;

		this.isLinkClicked = false;

		this.currentScale;

		var me = this;

		element.on('click', function() {
			var $elLink = element.find('.element3dtexts a');
			var elLinkTarget = $elLink.attr('target');

			if( !me.isLinkClicked ) $(me).trigger("onclick");
			me.isLinkClicked = false;

			if(elLinkTarget === '_self' || elLinkTarget === '_blank') {
				location.href = $elLink.attr('href');
			}
		});

		$(".js-content-link", element).on('click', function( evt ) {
			evt.preventDefault();
			me.isLinkClicked = true;
			$(me).trigger("onlinkclick");
		});
	}

	Element3d.prototype.showLoader = function()
	{
		$( "a", this.element ).addClass("contentlinkloader");
	}
	Element3d.prototype.hideLoader = function()
	{
		$( "a", this.element ).removeClass("contentlinkloader");
	}
	Element3d.prototype.getLoaderPosition = function()
	{
		var el = $( ".element3dtexts a", this.element );

		var  pos = el.offset();

		var offX = 15;
		var offY = 8;

		if( this.currentScale )
		{
			pos.left += (el.width()+offX) * this.currentScale;
			pos.top += offY * this.currentScale;
		}
		else
		{
			pos.left += el.width()+offX;
			pos.top += offY;
		}

		return pos;
	}
	Element3d.prototype.getHref = function()
	{
		return  $( ".js-content-link", this.element ).attr('href')
	}


	Element3d.prototype.setPosition = function( x, y, z )
	{
		this.position.setPosition( x, y, z );
	}

	Element3d.prototype.getPosition = function()
	{
		return this.position;
	}



	Element3d.prototype.render = function( p, scale, alpha, counter )
	{
		this.position2d = p;
		this.alpha = alpha;
		this.currentScale = scale;

		var zindex = 0;
		zindex = parseInt(scale*200)+600;
		this.zindex = zindex;

		if( alpha == 0 )
		{
			if( !this.isHidden ) Helpers.hide( this.element );
			this.isHidden == true;
		}
		else
		{
			Helpers.translate( this.element, p.x, p.y, 0, 0, scale, alpha, zindex );
			this.isHidden == false;
		}
	}

	return Element3d;
});

define(
	'app/3d/CameraSplines.class',['jquery', 'app/3d/Point3d.class', 'hv/util/MathX' ],
	function( $, Point3d, MathX ){



	function CameraSplines( points )
	{
		var a = [];
		for ( i=0; i<points.length ; i++ ) {
			a.push( points[i].position );
		}

		this.p = this.computeSmoothPath( a );
	}


	CameraSplines.prototype.computeSmoothPath = function( points ) {
		var px = [], py = [], pz = [], i;

		for ( i=0; i<points.length ; i++ ) {
			px[i] = points[i].x;
			py[i] = points[i].y;
			pz[i] = points[i].z;
		}
		var cx = this.computeControlPoints(px);
		var cy = this.computeControlPoints(py);
		var cz = this.computeControlPoints(pz);

		p = [];
		for ( i=0; i<points.length-1 ; i++ ) 
		{
			p.push( [ new Point3d( px[i], py[i], pz[i] ),
				new Point3d( cx.p1[i], cy.p1[i], cz.p1[i] ),
				new Point3d( cx.p2[i], cy.p2[i], cz.p2[i] ),
				new Point3d( px[i+1], py[i+1], pz[i+1] ) ]);
		}
		return p;
	}


	/*computes control points given knots K, this is the brain of the operation*/
	CameraSplines.prototype.computeControlPoints = function(K)
	{
		p1=[];
		p2=[];
		n = K.length-1;
		
		/*rhs vector*/
		a=[];
		b=[];
		c=[];
		r=[];
		
		/*left most segment*/
		a[0]=0;
		b[0]=2;
		c[0]=1;
		r[0] = K[0]+2*K[1];
		
		/*internal segments*/
		for (i = 1; i < n - 1; i++)
		{
			a[i]=1;
			b[i]=4;
			c[i]=1;
			r[i] = 4 * K[i] + 2 * K[i+1];
		}
				
		/*right segment*/
		a[n-1]=2;
		b[n-1]=7;
		c[n-1]=0;
		r[n-1] = 8*K[n-1]+K[n];
		
		/*solves Ax=b with the Thomas algorithm (from Wikipedia)*/
		for (i = 1; i < n; i++)
		{
			m = a[i]/b[i-1];
			b[i] = b[i] - m * c[i - 1];
			r[i] = r[i] - m*r[i-1];
		}

		p1[n-1] = r[n-1]/b[n-1];
		for (i = n - 2; i >= 0; --i)
			p1[i] = (r[i] - c[i] * p1[i+1]) / b[i];
			
		/*we have p1, now compute p2*/
		for (i=0;i<n-1;i++)
			p2[i]=2*K[i+1]-p1[i+1];
		
		p2[n-1]=0.5*(K[n]+p1[n-1]);
		
		return {p1:p1, p2:p2};
	}


	return CameraSplines;
});

define(
	'app/3d/Elements3d.class',['jquery', 'app/3d/Clouds3d.class', 'app/3d/Element3d.class', 'app/Helpers', 'app/3d/CameraSplines.class'],
	function( $, Clouds3d, Element3d, Helpers, CameraSplines ){


	var EL_Y_DIFF = 150;
	var EL_Z_DIFF = 5000;
	var EL_X_RAND = EL_Z_DIFF / 3;
	var EL_Y_RAND = 1000;

	var FRONT_DEFAULT_OFFSET_X = 0;
	var FRONT_DEFAULT_OFFSET_Y = -220;

	Elements3d.EL_Z_DIFF = EL_Z_DIFF;
	Elements3d.EL_Z_DIFF_LVL4 = EL_Z_DIFF*2;

	var LVL_Y_DIFF = 12000;

	var cameraSplines;

	var currentElement;


	function Elements3d( elementsData, math3d, camera3d )
	{
		this.elementsData = elementsData;

		this.elements = [];
		this.elementsHash = {};

		this.math3d = math3d;
		this.cont = $( "#elementscontainerid");

		this.camera3d = camera3d;

		this.levelsFirstElements = []

		this.closest;
		this.secondClosest;

		clouds3d = new Clouds3d( this.math3d );

		this.buildElements();
	}




	Elements3d.prototype.buildElements = function()
	{
		var me = this;
		var cont = $( "#elementscontainerid" );

		var currentLvl = 1;
		var currentLvlEl = 1;

		this.levelsFirstElements.push(0);

		/*
		<article class="element3dcont elementlevel1">
			<img class="element3dimage" src="../img/3dworldelements/level1icon.png">
			<div class="element3dtexts">
				<h1 class="element3dtitle">Ihr persönliches Refugium</h1>
				<a class="element3dlink">This is not a link</a>
			</div>
		</article>
		*/
		var z = 0;
		var i = 0;
		for ( i=0 ; i<this.elementsData.length ; i++ ) {
			var data = this.elementsData[i];

			addElement( i, data );
		}


		function addElement(i, data) {
			var el = data.el;
			var eId = data.id;
			var eLvl = data.level;
			var prev = me.elementsData[i-1] || {};
			var next = me.elementsData[i+1] || {};

			var e = new Element3d( eId, el );
			e.invisible = !!data.invisible;
			e.index = i;
			e.data = data;

			me.elementsHash[eId] = e;

			if( eLvl > currentLvl && e.invisible != true )
			{
				currentLvl = eLvl;
				currentLvlEl = i;
				me.levelsFirstElements.push(i);

				if( currentLvl == 4 && me.fourthLayerZ == undefined )
				{
					z -= EL_Z_DIFF*.5;
					me.fourthLayerZ = z;
				}
			}


			var ypos = Math.random()*EL_Y_RAND - EL_Y_RAND*.5 + i*EL_Y_DIFF + ( eLvl-1 )*LVL_Y_DIFF;

			var zpos = z, zdiff = EL_Z_DIFF;
			if ( eLvl == 1 ) {
				zdiff /= 1.4;
			}
			else if ( eLvl == 3  ) {
				zdiff /= 1.2;
			}
			else if( eLvl == 4  ) {
				zdiff = Elements3d.EL_Z_DIFF_LVL4;
			}

			if ( (Boolean(data.invisible) + Boolean(next.invisible)) === 1 ) {
				if( eLvl < 4) zdiff = EL_Z_DIFF / 1.5;
				else zdiff = EL_Z_DIFF / 5;
			}
			z -= zdiff;

			EL_X_RAND = zdiff / 3;

			var xpos = Math.random()*EL_X_RAND-EL_X_RAND*.5;

			//first VISIBLE element always in the centre
			if( i == 0 )
			{
				xpos = 0;
				ypos = i*EL_Y_DIFF + ( eLvl-1 )*LVL_Y_DIFF ;
			}

			// we want invisible elements to be in line with their
			// close neighbours
			if ( data.invisible && !prev.invisible ) {
				xpos = prev.position.x;
				ypos = prev.position.y;
			}
			else
			if ( !data.invisible && prev.invisible ) {
				prev.position.x = xpos;
				prev.position.y = ypos;
			}


			e.setPosition( xpos, ypos, zpos );
			me.elements.push( e );

			me.elementsData[i].position = e.getPosition();

			$(e).on("onclick", function( evt ){
				me.onElement(this);
			});

			if( eLvl == "1" )
			{
				$(e).on("onlinkclick", function( evt ){
					evt.preventDefault();
					me.onLvl1Anchor( this.index );
				});
			}
			else
			{
				$(e).on("onlinkclick", function( evt ){
					evt.preventDefault();
					me.onAnchor( this );
				});
			}

			var p = e.getPosition();

			var img = $( ".element3dimage", el );
			var pos = img.data("offset");
			if( pos ) {
				img.css({"margin": (-pos.y) + 'px ' + (-pos.x) + 'px'});
			}

			var additionalImg = $( ".element3dcloud", el );
			var pos = additionalImg.data("offset");
			if( pos ) {
				additionalImg.css({"margin": (-pos.y) + 'px ' + (-pos.x) + 'px'});
			}

			if( eLvl == "2" )
			{

				//clouds between elements
				var cloud;
				var numClouds = Math.random() * 4 + 4;
				for ( var j=0; j<numClouds; j++ ) {
					if ( Math.random() > 0.4 ) {
						if ( Math.random() > 0.3 ) {
							cloud = clouds3d.buildCloud( p.x + r(0,1500), p.y - 400 - Math.random() * 800, p.z + r(50,zdiff/1.2));
						} else {
							cloud = clouds3d.buildCloud( p.x + r(0,1500), p.y + 400 + Math.random() * 800, p.z + r(50,zdiff/1.2));
						}
					} else {
						cloud = clouds3d.buildCloud( p.x + r(500,2000), p.y + r(0,800), p.z + r(50,zdiff/1.2));
					}
					cloud.scale = 5 + Math.random() * ( Math.abs(cloud.position.x - p.x) / 300 * Math.abs(cloud.position.y - p.y) / 300 );
					cloud.$text.attr('for', eId);
				}
			}

			if(eLvl == "4") $(el).css({"display":"none"});
		}
		if( me.fourthLayerZ == undefined )
		{
			z -= EL_Z_DIFF*.5;
			me.fourthLayerZ = z;
		}

		this.maxZPos = z;

		//cameraSplines = new CameraSplines(this.elementsData);
		//this.camera3d.setSplinesData( cameraSplines.p );

	}

	function r(d1, d2) {
		var direction = Math.random() > 0.5 ? 1 : -1;
		return direction * (Math.random() * (d2-d1) + d1);
	};

	Elements3d.prototype.getMaxZPos = function()
	{
		return -this.maxZPos;
	};

	Elements3d.prototype.getFourthLayerZ = function()
	{
		return -this.fourthLayerZ;
	};


	Elements3d.prototype.onElement = function( el )
	{
		$(this).trigger("onclick", [el]);
	};
	Elements3d.prototype.onLvl1Anchor = function( id )
	{
		$(this).trigger("onlvl1linkclick", id );
	};
	Elements3d.prototype.onAnchor = function( el )
	{
		currentElement = el;
		el.showLoader();

		var pos = el.getLoaderPosition();

		$(this).trigger("onlinkclick", { href:el.getHref(), pos:pos } );
	};

	Elements3d.prototype.hideLoader = function()
	{
		currentElement.hideLoader();
	};



	Elements3d.prototype.render = function( counter )
	{
		clouds3d.render( counter );

		var i, e, p, pRot, pRotDiffX, p2, p2Diff, scale;

		var camZ = this.math3d.cameraPos.z;

		for( i = 0; i < this.elements.length; i++ )
		{
			e = this.elements[i];

			p = e.getPosition();

			pRot = this.math3d.rotate3d( p );
			p2 = this.math3d.project( pRot );

			scale = this.math3d.getScale( pRot, p2 );

			var alpha = this.math3d.getAlpha( pRot, scale );
			this.elementsData[i].alpha = alpha;

			p2 = this.math3d.addStagePosition( p2 );

			e.render( p2, scale, alpha, counter );
		}
	};



	Elements3d.prototype.getElementById = function(id)
	{
		return this.elementsHash[id];
	};

	Elements3d.prototype.findClosest = function()
	{
		var cameraZ = this.math3d.cameraPos.z;
		var closest = this.closest = this.findClosestElementAt(cameraZ);
		var closestDist = closest.getPosition().z + cameraZ;
		this.secondClosest = this.findClosestElement(function(e){
			var eDist = e.getPosition().z + cameraZ;
			var isOtherDirection = (eDist >= 0 && closestDist < 0) || (eDist < 0 && closestDist >= 0);
			return e != closest && isOtherDirection;
		});

		// in case camera is in front of first or behind last element
		if ( !this.secondClosest ) {
			this.secondClosest = this.findClosestElement(function(e){
				return e != closest;
			});
		}
	};


	Elements3d.prototype.findClosestElement = function(condition){
		return this.findClosestElementAt(this.math3d.cameraPos.z, condition);
	};

	Elements3d.prototype.findClosestElementAt = function(z, condition)
	{
		var closest= -1;
		var minDist = 1000000000;


		var i, d;

		for( i=0; i<this.elements.length; i++)
		{
			d = Math.abs( z + this.elements[i].getPosition().z )
			if( d < minDist && (!condition || condition(this.elements[i])) )
			{
				closest = i;
				minDist = d;
			}
		}

		return this.elements[closest];
	};


	Elements3d.prototype.isClosestVisible = function()
	{
		var e = this.closest;

		if( e == undefined ) return false;
		if( e.alpha < 1 ) return false;

		var p = e.position2d;
		if( p.x < 0 || p.x > this.math3d.windowW || p.y <0 || p.y > this.math3d.windowH )
		{
			return false;
		}

		return true;
	};

	Elements3d.prototype.getLevelFirstElement = function( lvlId )
	{
		return this.levelsFirstElements[ lvlId -1 ];
	};

	Elements3d.prototype.getElementPos = function( index )
	{
		return this.getElement(index).getPosition();
	};

	Elements3d.prototype.getElementHref = function( index )
	{
		return this.getElement(index).getHref();
	};

	Elements3d.prototype.getLoaderPosition = function( index )
	{
		currentElement = this.getElement(index);
		currentElement.showLoader();
		return this.getElement(index).getLoaderPosition();
	};

	Elements3d.prototype.getElement = function(id_or_index) {
		return this.elements[id_or_index] || this.elementsHash[id_or_index];
	};



	return Elements3d;
});

define(
	'app/3d/Line3d.class',['jquery', 'app/Helpers', 'app/Config'],
	function( $, Helpers, Config ){

	var globA = .4;

	var cGrey = "100, 100, 100, ";
	var cRed = "204, 0, 0, ";


	function Line3d( from, to , bezier1, bezier2, fromId, toId, cont )
	{
		this.from = from;
		this.to = to;
		this.bezier1 = bezier1;
		this.bezier2 = bezier2;
		this.fromId = fromId;
		this.toId = toId;
		this.cont = cont;
		this.innetCont;

		this.isHidden = true;
		this.isHighlighted = false;
		this.isOver = false;
		this.isLineHidden = false;
		this.isRouteNetworkHidden = false;


		this.createElementDiv();
	}


	Line3d.prototype.render = function( ctx, pFrom, pTo, pB1, pB2, a1, a2, linesA )
	{
		if( a1<=0.2 ) a1=.2;
		if( a2<=0.2 ) a2=.2;

		/*
		ctx.beginPath();
		ctx.lineWidth="1";
		ctx.strokeStyle="green";
		ctx.rect(pFrom.x-2,pFrom.y-2,4,4);
		ctx.stroke();
		ctx.beginPath();
		ctx.lineWidth="1";
		ctx.strokeStyle="red";
		ctx.rect(pTo.x-2,pTo.y-2,4,4);
		ctx.stroke();
		*/

		ctx.beginPath();
		ctx.strokeStyle = '#cccccc';
		ctx.moveTo( pFrom.x, pFrom.y );

		var c = cGrey;
		if( this.isOver || this.isHighlighted && ( this.toElementId == this.targetId ) )
		{
			c = cRed;
			globA = .4;
		}
		else
		{
			globA = .2;
		}

		var rad = ctx.createLinearGradient(pFrom.x, pFrom.y,  pTo.x,  pTo.y );
		rad.addColorStop(0, 'rgba('+c+(+(a1*globA*linesA).toFixed(5))+')');
		rad.addColorStop(1, 'rgba('+c+(+(a2*globA*linesA).toFixed(5))+')');

		ctx.strokeStyle = rad;

		if( pB2 ){ ctx.bezierCurveTo( pB1.x, pB1.y, pB2.x, pB2.y, pTo.x, pTo.y ); }
		else if( pB1 ){ ctx.quadraticCurveTo( pB1.x, pB1.y, pTo.x, pTo.y ); }
		else { ctx.lineTo( pTo.x, pTo.y ); }

		ctx.stroke();
	}


	Line3d.prototype.setTxt = function( p, txt, isRight, targetId )
	{
		this.targetId = targetId;

		if( this.isHighlighted )
		{
			if( this.toElementId == this.targetId )
			{
				var a = Config.get('langThemerouteNext').split("%name%");
				if( a.length > 1 )
				{
					txt = "<span class='nextitem'>" + a[0] + txt + a[1] + "</span>";
				}
				else
				{
					txt = "<span class='nextitem'>" + a[0] + txt + "</span>";
				}
			}
			else
			{
				var a = Config.get('langThemeroutePrev').split("%name%");
				if( a.length > 1 )
				{
					txt = "<span class='previtem'>" + a[0] + txt + a[1]+ "</span>";
				}
				else
				{
					txt = "<span class='previtem'>" + a[0] +  txt + "</span>";
				}
			}
		}


		this.$innerCont.html(txt);

		this.showLabel();

		if(isRight)
		{
			p.x -= this.$text.width()+20;
		}

		if(this.$text) Helpers.translate( this.$text[0], p.x+10, p.y, 0, 0, 1 );
	}


	Line3d.prototype.createElementDiv = function()
	{
		this.$text = $('<div class="worlds3dlabel"></div>');
		this.$innerCont = $('<a class="world3dlabeltext"></a>');
		this.$text.append(this.$innerCont);

		this.cont.append( this.$text );

		this.$text.css({
			'opacity':0,
			'display': 'none'
		});

		this.addMouseHandlers();
	}


	Line3d.prototype.addMouseHandlers = function()
	{
		var me = this;

		this.$text.on( "click",  function(e)
		{
			e.preventDefault();
			me.dispatchClick();

			me.isMouseDown = false;
		});

		this.$text.on( "mousedown",  function(e)
		{
			me.isMouseDown = true;
		});

		this.$text.on( "mouseup",  function(e)
		{
			if( me.isMouseDown == true )
			{
				e.preventDefault();
				me.dispatchClick();
			}

			me.isMouseDown = false;
		});

		this.$text.on( "mouseenter", function(){ me.onMouseEnter(); } );
		this.$text.on( "mouseleave", function(){ me.onMouseLeave(); me.isMouseDown = false; } );

	};

	Line3d.prototype.onMouseEnter = function()
	{
		this.isOver = true;
	};

	Line3d.prototype.onMouseLeave = function()
	{
		this.isOver = false;
	};

	Line3d.prototype.dispatchClick = function()
	{
		this.$text.trigger("onclick", [this.targetId]);
		this.$text.trigger("wos-worlds3d-label-click");
	};


	Line3d.prototype.hideLabel = function()
	{
		if(!this.isHidden )
		{
			this.$text.stop().animate({'opacity':0 }, { duration:100,
				complete: function() {
	      		$(this).css({
						'display': 'none'
				})
   			 } });

			this.isHidden = true;
		}
	}

	Line3d.prototype.showLabel = function()
	{
		if( this.isHidden && this.isRouteNetworkHidden == false )
		{
			this.$text.animate({'opacity':1}, 400).css({
					'display': 'block'
			});
			this.isHidden = false;
		}
	}


	Line3d.prototype.highlight = function( id )
	{
		this.isHighlighted = true;
		this.toElementId = id;
		this.$text.addClass('highlighted');
	}


	Line3d.prototype.dehighlight = function()
	{
		this.isHighlighted = false;
		this.$text.removeClass('highlighted');
	}

	Line3d.prototype.hide = function()
	{
		this.isLineHidden = true;
	}

	Line3d.prototype.show = function()
	{
		this.isLineHidden = false;
	}

	Line3d.prototype.hideRouteNetwork = function()
	{
		this.isRouteNetworkHidden = true;
	}



	return Line3d;
});

define(
	'app/3d/Lines3d.class',['jquery', 'app/3d/Point.class', 'app/3d/Point3d.class', 'app/3d/Line3d.class', 'hv/util/MathX', 'app/Config' ],
	function( $, Point, Point3d, Line3d, MathX, Config ){


	var lmarginTop = 10;
	var lmarginBottom = 29;
	var lmarginLeft = 10;
	var lmarginRight = 50;

	var labelsTimerId;
	var isLabelsTimer = false;
	var currentClosest = -100;
	var linesA = 0;

	
	function Lines3d( elements, elementsData, connectionsData, autoroutesData, ctx, math3d )
	{
		this.elements = elements;
		this.elementsData = elementsData;
		this.connections = [];
		this.connectionsData = connectionsData;
		this.autoroutesData = autoroutesData;

		this.isRouteHighlighted = false;

		this.routeData;

		this.ctx = ctx;
		this.math3d = math3d;

		this.cont = $( "#labelscontainerid" );

		this.buildAutoConnections();
	}


	Lines3d.prototype.buildAutoConnections = function()
	{
		var me = this;
		var besPos = .3;
		
		for( var i = 0; i< this.connectionsData.length; i++ )
		{			

			var fromId = this.getElementById( this.connectionsData[i].id1 );
			var toId =this.getElementById( this.connectionsData[i].id2 );

			if(fromId == -1 || toId == -1 || this.elementsData[toId].el.hasClass("is-dummy")) continue;
			var d = -90;
			if( +this.elementsData[ fromId ].level == 1) d = 27;

			var fromData = this.elements[ fromId ].getPosition();
			var from = new Point3d( fromData.x, fromData.y+d, fromData.z );

			var toData = this.elements[ toId ].getPosition();
			var to = new Point3d( toData.x, toData.y-90, toData.z );

			var d = -500;
			if( +this.elementsData[ fromId ].level == 1) d = 500;

			var bezier1 = new Point3d( from.x, from.y +d, from.z );
			var bezier2 = new Point3d( to.x, to.y-500, to.z );
			//var bezier1 = new Point3d( from.x, from.y, from.z );
			//var bezier2 = new Point3d( to.x, to.y, to.z );
			
			var e = new Line3d( from, to, bezier1, bezier2, fromId, toId, this.cont );

			e.$text.bind( "onclick", function( e, targetId ) {
				$( me ).trigger("onclick", [targetId]);
			});

			this.connections.push( e );

			if( Config.get("isRouteNetworkOff") == "true" )
			{
				if( +this.elementsData[ fromId ].level == 4 || +this.elementsData[ toId ].level == 4 
					|| +this.elementsData[ fromId ].level == undefined || +this.elementsData[ toId ].level == undefined )
				{
					e.hideRouteNetwork();
				}
			}

		}
	}


	Lines3d.prototype.setLabelsTimer = function()
	{		
		linesA = 0;
		isLabelsTimer = true;
	}
	
	function cycleInc(n, d) {
		d /= 1.5;
		n += (n ? n / Math.abs(n) : 1) * d;
		n *= -1;
		return n;
	}


	Lines3d.prototype.renderConnections = function( closest, isClosestVisible )
	{
		var e, f, t, b1, b2, p;

		var xtop = 0, xbottom = xtop;
		var xmid = 0;
		var yleft = 0, yright = yleft;

		var a1, a2;

		// view borders positions.
		var lX = [ [0, this.math3d.windowW], [0, this.math3d.windowW], [lmarginLeft, lmarginLeft], [this.math3d.windowW-lmarginRight, this.math3d.windowW-lmarginRight] ];
		var lY = [ [lmarginTop, lmarginTop], [ this.math3d.windowH-lmarginBottom, this.math3d.windowH-lmarginBottom ], [ 0, this.math3d.windowH ], [ 0, this.math3d.windowH ] ];			

		var labelsPos = [];

		var currentLvl = this.elementsData[ closest ].level;

		if( currentClosest != closest )
		{
			currentClosest = closest;
			isLabelsTimer = false;

			if(labelsTimerId) clearTimeout( labelsTimerId );

			labelsTimerId = setTimeout( this.setLabelsTimer, 250 );
		}


		linesA += (1-linesA)/20;


		for( var i = 0; i < this.connections.length; i++ )
		{

			e = this.connections[i];

			if( e.isLineHidden || e.isRouteNetworkHidden ) continue;

			if(!isLabelsTimer)
			{
				e.hideLabel();
				continue;
			}

			var fromid = e.fromId;
			var toid = e.toId;

			if( fromid != closest && toid != closest ) continue;


			var rotFrom = this.math3d.rotate3d( e.from );
			var rotTo = this.math3d.rotate3d( e.to );

			f = this.math3d.addStagePosition( this.math3d.project( rotFrom ) );
			t = this.math3d.addStagePosition( this.math3d.project( rotTo ) );

			//
			var dist = Math.sqrt( MathX.distance3d(e.from, e.to) );
			
			b1 = null;
			if( e.bezier1 ){
				b1 = this.math3d.rotate3d( e.bezier1 );
				b1 = this.math3d.addStagePosition( this.math3d.project( b1 ) );
			}

			b2 = null;
			if( e.bezier2 ){
				b2 = this.math3d.rotate3d( e.bezier2 );
				b2 = this.math3d.addStagePosition( this.math3d.project( b2 ) );
			}

			a1 = this.elementsData[ e.fromId ].alpha || 0;
			a2 = this.elementsData[ e.toId ].alpha || 0;

			var isShowLine = ( a1 != 0 || a2 != 0 );


			//
			// fakes lines positions.
			// if link points to the level up - it's always on top.
			// if link points to the level below - it's always at the bottom.
			// if link points to the same level, but to the element that's behind the view -
			// - it's always left or right.
			//
			var lvlfrom = this.elementsData[ fromid ].level;
			var lvlclosest = this.elementsData[ closest ].level;
			var lvlto = this.elementsData[ toid ].level;

			var cameraZ = this.math3d.cameraPos.z;

			var DIF = 1000;
			
			if( toid == closest )
			{
				if( lvlfrom > lvlclosest )
				{
					//level up
					f.y = Math.min(f.y, -DIF);
					b1.y = Math.min(b1.y, -DIF);
					f.x += xtop;
					b1.x += xtop;
					xtop = cycleInc(xtop, dist);
				}
				else if( lvlfrom < lvlclosest )
				{
					//level down
					f.y = Math.max( f.y, this.math3d.windowH + DIF);
					b1.y = Math.max( b1.y, this.math3d.windowH + DIF);
					f.x += xbottom;
					b1.x += xbottom;
					xbottom = cycleInc(xbottom, dist*5);
				}
				else
				{
					//same level
					f.y = MathX.range( f.y, 20,  this.math3d.windowH*.6);
					b1.y = MathX.range( b1.y, 20,  this.math3d.windowH*.6);
					f.x += xmid;
					b1.x += xmid;
					xmid = cycleInc(xmid, dist);

					if( fromid < closest )
					{
						//behind the view
						if( e.from.x < e.to.x )
						{
							f.x = Math.min(f.x, -DIF);
							b1.x = Math.min(b1.x, -DIF);
							f.y += yleft;
							b1.y += yleft;
							yleft = cycleInc(yleft, dist);
						}
						else
						{
							f.x = Math.max(f.x, this.math3d.windowW + DIF);
							b1.x = Math.max(b1.x, this.math3d.windowW + DIF);
							f.y += yright;
							b1.y += yright;
							yright = cycleInc(yright, dist);
						}
					}
				}
			}
			else if( fromid == closest )
			{
				if( lvlto > lvlclosest )
				{
					//level up
					t.y = Math.min(f.y, -DIF);
					b2.y = Math.min(b2.y, -DIF);
					t.x += xtop;
					b2.x += xtop;
					xtop = cycleInc(xtop, dist);
				}
				else if( lvlto < lvlclosest )
				{
					//level down
					t.y = Math.max(t.y, this.math3d.windowH + DIF);
					b2.y = Math.max(b2.y, this.math3d.windowH + DIF);
					t.x += xbottom;
					b2.x += xbottom;
					xbottom = cycleInc(xbottom, dist*5);
				} 
				else
				{
					//same level
					t.y = MathX.range( t.y, 20,  this.math3d.windowH*.6);
					b2.y = MathX.range( b2.y, 20,  this.math3d.windowH*.6);
					t.x += xmid;
					b2.x += xmid;
					xmid = cycleInc(xmid, dist);

					if( toid < closest )
					{
						//behind the view
						if( e.to.x < e.from.x )
						{
							t.x = Math.min(t.x, - DIF);
							b2.x = Math.min(b2.x, - DIF);
							t.y += yleft;
							b2.y += yleft;
							yleft = cycleInc(yleft, dist);
						}
						else
						{
							t.x = Math.max(t.x, this.math3d.windowW + DIF);
							b2.x = Math.max(b2.x, this.math3d.windowW + DIF);
							t.y += yright;
							b2.y += yright;
							yright = cycleInc(yright, dist);
						}
					}
				}
			}

			
			//
			// labels
			//
			if( isShowLine && isClosestVisible && ( ( e.fromId == closest ) || ( e.toId == closest ) ) && isLabelsTimer )
			{
				var p = new Point();

				if( f.x>lmarginLeft && f.x<this.math3d.windowW-lmarginRight && 
					f.y>lmarginTop && f.y<this.math3d.windowH-lmarginBottom &&  
					t.x>lmarginLeft && t.x<this.math3d.windowW-lmarginRight && 
					t.y>lmarginTop && t.y<this.math3d.windowH-lmarginBottom )
				{
					//link is in the middle of the screen.
					if( e.fromId == closest )
					{
						var ty = 't';
						p.x = t.x;
						p.y = t.y;
					}
					else
					{
						var ty = 'f';
						p.x = f.x;
						p.y = f.y;
					}

					var M_X = 700;
					var M_Y = 600;
					if( Math.abs( p.x-this.math3d.centerX ) < M_X*.5 )
					{
						//
						//but we don't want the link to be in the center of the screen and overlay the main element!
						//
						p.y = MathX.outsideRange( p.y, this.math3d.centerY-M_Y*.5, this.math3d.centerY+M_Y*.8 );
						
						if(ty == 't' ) t.y = p.y;
						else f.y = p.y;
					}

				}
				else
				{

					//
					//now we know that the link points outside of the view.
					//let's find intersections of the line and screen borders.
					//

					var el = new Point();
					if( e.fromId == closest )
					{
						el.x = f.x;
						el.y = f.y;
					}
					else
					{
						el.x = t.x;
						el.y = t.y;
					}

					var bX = [f.x, b1.x, b2.x, t.x];
					var bY = [f.y, b1.y, b2.y, t.y];

					var minDist = 100000000;
		   			var minDistId = 0;
		    		var dPoints = [];
					
					for( var j=0; j<4; j++ )
					{
						var lp = MathX.computeIntersections( bX, bY, lX[j], lY[j], el, this.ctx);

						var d = MathX.distance( lp, el );
						
						if( d< minDist && 
							( lp.x <= lmarginLeft+10 ||  
								lp.x >= this.math3d.windowW-lmarginRight-10 || 
								lp.y <= lmarginTop+10 || 
								lp.y >= this.math3d.windowH-lmarginBottom-10 ) )
						{
							minDist = d;
							minDistId = j;
						}

						dPoints.push( lp );
					}

					p = dPoints[minDistId];
				}

				var txt;
				var targetId;
				if( e.fromId == closest )
				{
					txt = this.elementsData[e.toId].title;
					targetId = e.toId;
				}
				else
				{
					txt = this.elementsData[e.fromId].title;
					targetId = e.fromId;
				}

				p.x = MathX.range( p.x, lmarginLeft, this.math3d.windowW - lmarginRight );
				p.y = MathX.range( p.y, lmarginTop, this.math3d.windowH - lmarginBottom );	

				// check if labels overlay themselves
				p = this.checkLabelsPos( p, labelsPos );

				labelsPos.push( p );

				//
				// render label
				//
				e.setTxt( p, txt, (minDistId==3)?true:false, targetId);		
			}
			else
			{
				e.hideLabel();
			}


			//
			// render line
			//
			if( isShowLine ) 
			{
				e.render( this.ctx, f, t, b1, b2, a1, a2, linesA );
			}

		}
	}


	Lines3d.prototype.checkLabelsPos = function( p, labelsPos, isUp )
	{
		for( var i=0; i < labelsPos.length; i++ )
		{
			if( Math.abs( p.y-labelsPos[i].y ) < 13 && Math.abs( p.x-labelsPos[i].x ) < 150  )
			{
				if( p.y > this.math3d.windowH*.8 || isUp == true )
				{
					p.y -= 15;
					p= this.checkLabelsPos( p, labelsPos, true );
				}
				else
				{
					p.y += 15;
					p= this.checkLabelsPos( p, labelsPos );
				}				
			}
		}

		return p;
	}
	

	Lines3d.prototype.getElementById = function( id )
	{
		for( var i =0; i < this.elementsData.length; i++ )
		{
			if( this.elementsData[i].id == id ) return i;
		}
		return -1;
	};


	Lines3d.prototype.highlightRoute = function( routeData )
	{
		this.isRouteHighlighted = true;
		
		for( var i = 0; i<routeData.length-1; i++ )
		{
			var from = routeData[i];
			var to = routeData[i+1];

			for( var j = 0; j< this.connectionsData.length; j++ )
			{
				if( this.connectionsData[j].id1 == from && this.connectionsData[j].id2 == to )
				{
					this.connections[j].highlight( this.getElementById( to ) );
				}
			}
		}

		for( var i = 0; i< this.connections.length; i++ )
		{	
			if( this.connections[i].isHighlighted != true ) this.connections[i].hide();
		}	
	};

	Lines3d.prototype.dehighlightRoute = function()
	{
		if( this.isRouteHighlighted == true )
		{
			for( var i = 0; i< this.connections.length; i++ )
			{	
				this.connections[i].dehighlight();
				this.connections[i].show();
			}

			this.isRouteHighlighted = false;
		}		
	};


	return Lines3d;
});

define (
	'app/modules/BgImgData.class',['jquery', 'hv/util/MathX' ],
	function( $, MathX ){




	function BgImgData()
	{	
		this.w;
		this.h;

		this.img;
		this.cont;

		this.isLoaded = false;
		this.isHidden = false;

		this.imgW;
		this.imgH;

		this.x;
		this.y;

		this.tDifX =0;
		this.tDifY =0;
		this.difX =0;
		this.difY =0;

		this.s;
	}

	

	return BgImgData;
});

define (
	'app/modules/BackgroundImg2.class',['jquery', 'hv/util/MathX', 'app/Helpers', 'app/Config', 'app/modules/BgImgData.class' ],
	function( $, MathX, Helpers, Config, BgImgData){


 
	function BackgroundImg2( id, img, cont )
	{
		this.imgData = new BgImgData();

		this.imgData.img = img;
		this.imgData.cont =  cont;

		this.id = id;

		this.init();
	}


	BackgroundImg2.prototype.init = function()
	{
		this.imgData.isLoaded = true;

		this.imgData.imgW = this.imgData.img.width();
		this.imgData.imgH = this.imgData.img.height();

		this.rescale( $(window).width(), $(window).height() );
	}


	BackgroundImg2.prototype.rescale = function( windowW, windowH )
	{
		this.windowW = windowW;
		this.windowH = windowH;
		
		if( !this.imgData.isLoaded ) return;

		if( this.id == "alps" || this.id == "matterhorn" )
		{
			this.imgData.w = this.windowW*1.1;

			this.imgData.s = this.imgData.w/this.imgData.imgW;
			this.imgData.h = this.imgData.imgH * this.imgData.s;
		}
		else 
		{
			this.imgData.w = this.windowW*1.1;

			this.imgData.s = this.imgData.w/this.imgData.imgW;
			this.imgData.h = this.imgData.imgH * this.imgData.s;
		}
	}

	
	BackgroundImg2.prototype.setPositionDif = function( x, y )
	{
		this.imgData.tDifX = x;
		this.imgData.tDifY = y;
	}


	BackgroundImg2.prototype.setPos = function( posX, posY, posZ, fourthLevelPos )
	{
		if( !this.imgData.isLoaded ) return;

		var x = 0;
		var y = 0;
		var s = this.imgData.s;
		var a = 1;

		this.imgData.difX += (this.imgData.tDifX - this.imgData.difX)/10;
		this.imgData.difY += (this.imgData.tDifY - this.imgData.difY)/10;

		//horizon, far, mid, near, alps, matternhorn 
		if( this.id == "matterhorn" )
		{
			posZ = Math.min(posZ, 50000);
			s = this.imgData.s + Math.min( (posZ+5000)/110000, 1.2 );

			y = this.windowH - this.imgData.h*.95 - this.imgData.h*.7 *( ( posY-300 )/10000 + posZ/300000 );
			y = Math.max(y, this.windowH - this.imgData.h );
		
			x = (this.windowW-this.imgData.imgW*s)/2-this.imgData.w*0.05*posX/2000;
			x = MathX.range(x, -(this.imgData.imgW*s-this.windowW), 0);

			x+=5*this.imgData.difX;
			y+=-2.5*this.imgData.difY;
		}
		else if( this.id == "alps" )
		{
			posZ = Math.min(posZ, 50000);
			s = this.imgData.s + (posZ+5000)/190000;

			y = this.windowH - this.imgData.h*.86 - this.imgData.h *( ( posY-300 )/15000 - posZ/300000 );
			y = Math.max(y, this.windowH - this.imgData.h );
		
			x = (this.windowW-this.imgData.imgW*s)/2-this.imgData.w*0.05*posX/4000;
			x = MathX.range(x, -(this.imgData.imgW*s-this.windowW), 0);

			x+=5*this.imgData.difX/1.5;
			y+=-2.5*this.imgData.difY/1.5;
		}
		else if( this.id == "near" )
		{
			posY = Math.max(posY, -30000);
			y = this.windowH*.5 - this.imgData.h*.52 - this.imgData.h * ( posY+16000 )/24000;

			s = this.imgData.s + (posZ+5000)/190000;

			if( posZ > fourthLevelPos-7000 )
			{
				var d = (posZ - (fourthLevelPos-7000));
				y -= (d/3);
				s += d/4000;
			}

			x = (this.windowW-this.imgData.imgW*s)/2-this.imgData.w*0.05*posX/2000;
			x = MathX.range(x, -(this.imgData.imgW*s-this.windowW), 0);

			x+=5*this.imgData.difX;
			y+=-2.5*this.imgData.difY;
		}
		else if( this.id == "mid" )
		{
			posY = Math.max(posY, -30000);
			y = this.windowH*.5 - this.imgData.h*.52 - this.imgData.h * ( posY+16000 )/32000;

			s = this.imgData.s + (posZ+5000)/190000;

			if( posZ > fourthLevelPos-7000 )
			{
				var d = (posZ - (fourthLevelPos-7000));
				y -= (d/4.5);
				s += d/6000;
			}

			x = (this.windowW-this.imgData.imgW*s)/2-this.imgData.w*0.05*posX/3000;
			x = MathX.range(x, -(this.imgData.imgW*s-this.windowW), 0);

			x+=5*this.imgData.difX/1.5;
			y+=-2.5*this.imgData.difY/1.5;

		}
		else if( this.id == "far" )
		{
			posY = Math.max(posY, -30000);
			y = this.windowH*.5 - this.imgData.h*.52 - this.imgData.h * ( posY+16000 )/35000;

			s = this.imgData.s + (posZ+5000)/190000;

			if( posZ > fourthLevelPos-7000 )
			{
				var d = (posZ - (fourthLevelPos-7000));
				y -= (d/7);
				s += d/8000;
			}

			x = (this.windowW-this.imgData.imgW*s)/2-this.imgData.w*0.05*posX/4000;
			x = MathX.range(x, -(this.imgData.imgW*s-this.windowW), 0);

			x+=5*this.imgData.difX/3;
			y+=-2.5*this.imgData.difY/3;	
		}
		else if( this.id == "horizon" )
		{
			posY = Math.max(posY, -30000);
			y = this.windowH*.5 - this.imgData.h*.48 - this.imgData.h * ( posY+16000 )/250000;

			if( posZ > fourthLevelPos-7000 )
			{
				var d = (posZ - (fourthLevelPos-7000));
				y -= (d/9);
				a = 1-Math.abs(d/3000);
			}

			x = (this.windowW-this.imgData.imgW*s)/2-posX/200;
			x = MathX.range(x, -(this.imgData.imgW*s-this.windowW), 0);
	
		}
		else if( this.id == "level" )
		{
			if( posZ > fourthLevelPos-7000 )
			{
				var d = (posZ - (fourthLevelPos-7000));
				y = this.windowH - (d/5500)*(this.windowH+this.imgData.h);
				
				a = 1-Math.abs(d/27000);
				x = (this.windowW-this.imgData.imgW*s)/2-posX/200;

				s = this.imgData.s + d/9000;
			}
			else
			{
				y = -100000;
			}
		}

		var toHide = false;
		if( x < -this.imgData.w*s || x > this.windowW || y< -this.imgData.h*s || y>this.windowH ) toHide = true;

		if( toHide == true )
		{
			if( this.imgData.isHidden == false )
			{
				this.imgData.isHidden = true;
				Helpers.hide( this.imgData.cont[0] );
			}
		}
		else
		{
			if( this.imgData.isHidden == true )
			{
				this.imgData.isHidden = false;
				Helpers.show( this.imgData.cont[0] );
			}

			Helpers.translate( this.imgData.cont[0], x, y, 0, 0, s, a );
		}

		
	}


	return BackgroundImg2;
});

define (
	'app/modules/Background2.class',['jquery', 'hv/util/MathX', 'app/Helpers', 'app/Config', 'app/modules/BackgroundImg2.class' ],
	function( $, MathX, Helpers, Config, BackgroundImg2 ){

	var windowWidth = $(window).width();
	var windowHeight = $(window).height();

	var bgImgs = []


	function Background2( fourthLevelPos )
	{
		this.fourthLevelPos = fourthLevelPos;

		this.c = $("#worldbackground2id");

		var me = this;
		$(window).on('resize', function(){
			me.rescale();
		});

		this.build();

		this.rescale();
	}

 
	Background2.prototype.build = function()
	{

		var horizon = new BackgroundImg2( "horizon", $( ".bghorizonimg", this.c ), $( ".bghorizoncont", this.c ) );
		var far = new BackgroundImg2( "far", $( ".bgfarimg", this.c ), $( ".bgfarcont", this.c ) );
		var mid = new BackgroundImg2( "mid", $( ".bgmidimg", this.c ), $( ".bgmidcont", this.c ) );
		var near = new BackgroundImg2( "near", $( ".bgnearimg", this.c ), $( ".bgnearcont", this.c ) );
		var alps = new BackgroundImg2( "alps", $( ".bgalpsimg", this.c ), $( ".bgalpscont", this.c ) );
		var matternhorn = new BackgroundImg2( "matterhorn", $( ".bgmatterhornimg", this.c ), $( ".bgmatterhorncont", this.c ) );
		
		var level = new BackgroundImg2( "level", $( ".bglevelimg", this.c ), $( ".bglevelcont", this.c ) );

		bgImgs.push( horizon, far, mid, near, alps, matternhorn, level );
	}


	Background2.prototype.setPos = function( posX, posY, posZ, level )
	{
		for( var i=0; i<bgImgs.length; i++ )
		{
			bgImgs[i].setPos( posX, posY, posZ, this.fourthLevelPos, level );
		}
	}

	Background2.prototype.setPositionDif = function( pX, pY )
	{
		for( var i=0; i<bgImgs.length; i++ )
		{
			bgImgs[i].setPositionDif( pX, pY );
		}
	}


	Background2.prototype.rescale = function()
	{
		this.windowW = $(window).width();
		this.windowH = $(window).height();

		for( var i=0; i<bgImgs.length; i++ )
		{
			bgImgs[i].rescale( this.windowW, this.windowH );
		}
	}


	return Background2;
});

/*
 * jQuery EasIng v1.2 - http://gsgd.co.uk/sandbox/jquery.easIng.php
 *
 * Uses the built In easIng capabilities added In jQuery 1.1
 * to offer multiple easIng options
 *
 * Copyright (c) 2007 George Smith
 * Licensed under the MIT License:
 *   http://www.opensource.org/licenses/mit-license.php
 */

// t: current time, b: begInnIng value, c: change In value, d: duration

jQuery.extend( jQuery.easing,
{
	easeInQuad: function (x, t, b, c, d) {
		return c*(t/=d)*t + b;
	},
	easeOutQuad: function (x, t, b, c, d) {
		return -c *(t/=d)*(t-2) + b;
	},
	easeInOutQuad: function (x, t, b, c, d) {
		if ((t/=d/2) < 1) return c/2*t*t + b;
		return -c/2 * ((--t)*(t-2) - 1) + b;
	},
	easeInCubic: function (x, t, b, c, d) {
		return c*(t/=d)*t*t + b;
	},
	easeOutCubic: function (x, t, b, c, d) {
		return c*((t=t/d-1)*t*t + 1) + b;
	},
	easeInOutCubic: function (x, t, b, c, d) {
		if ((t/=d/2) < 1) return c/2*t*t*t + b;
		return c/2*((t-=2)*t*t + 2) + b;
	},
	easeInQuart: function (x, t, b, c, d) {
		return c*(t/=d)*t*t*t + b;
	},
	easeOutQuart: function (x, t, b, c, d) {
		return -c * ((t=t/d-1)*t*t*t - 1) + b;
	},
	easeInOutQuart: function (x, t, b, c, d) {
		if ((t/=d/2) < 1) return c/2*t*t*t*t + b;
		return -c/2 * ((t-=2)*t*t*t - 2) + b;
	},
	easeInQuint: function (x, t, b, c, d) {
		return c*(t/=d)*t*t*t*t + b;
	},
	easeOutQuint: function (x, t, b, c, d) {
		return c*((t=t/d-1)*t*t*t*t + 1) + b;
	},
	easeInOutQuint: function (x, t, b, c, d) {
		if ((t/=d/2) < 1) return c/2*t*t*t*t*t + b;
		return c/2*((t-=2)*t*t*t*t + 2) + b;
	},
	easeInSine: function (x, t, b, c, d) {
		return -c * Math.cos(t/d * (Math.PI/2)) + c + b;
	},
	easeOutSine: function (x, t, b, c, d) {
		return c * Math.sin(t/d * (Math.PI/2)) + b;
	},
	easeInOutSine: function (x, t, b, c, d) {
		return -c/2 * (Math.cos(Math.PI*t/d) - 1) + b;
	},
	easeInExpo: function (x, t, b, c, d) {
		return (t==0) ? b : c * Math.pow(2, 10 * (t/d - 1)) + b;
	},
	easeOutExpo: function (x, t, b, c, d) {
		return (t==d) ? b+c : c * (-Math.pow(2, -10 * t/d) + 1) + b;
	},
	easeInOutExpo: function (x, t, b, c, d) {
		if (t==0) return b;
		if (t==d) return b+c;
		if ((t/=d/2) < 1) return c/2 * Math.pow(2, 10 * (t - 1)) + b;
		return c/2 * (-Math.pow(2, -10 * --t) + 2) + b;
	},
	easeInCirc: function (x, t, b, c, d) {
		return -c * (Math.sqrt(1 - (t/=d)*t) - 1) + b;
	},
	easeOutCirc: function (x, t, b, c, d) {
		return c * Math.sqrt(1 - (t=t/d-1)*t) + b;
	},
	easeInOutCirc: function (x, t, b, c, d) {
		if ((t/=d/2) < 1) return -c/2 * (Math.sqrt(1 - t*t) - 1) + b;
		return c/2 * (Math.sqrt(1 - (t-=2)*t) + 1) + b;
	},
	easeInElastic: function (x, t, b, c, d) {
		var s=1.70158;var p=0;var a=c;
		if (t==0) return b;  if ((t/=d)==1) return b+c;  if (!p) p=d*.3;
		if (a < Math.abs(c)) { a=c; var s=p/4; }
		else var s = p/(2*Math.PI) * Math.asin (c/a);
		return -(a*Math.pow(2,10*(t-=1)) * Math.sin( (t*d-s)*(2*Math.PI)/p )) + b;
	},
	easeOutElastic: function (x, t, b, c, d) {
		var s=1.70158;var p=0;var a=c;
		if (t==0) return b;  if ((t/=d)==1) return b+c;  if (!p) p=d*.3;
		if (a < Math.abs(c)) { a=c; var s=p/4; }
		else var s = p/(2*Math.PI) * Math.asin (c/a);
		return a*Math.pow(2,-10*t) * Math.sin( (t*d-s)*(2*Math.PI)/p ) + c + b;
	},
	easeInOutElastic: function (x, t, b, c, d) {
		var s=1.70158;var p=0;var a=c;
		if (t==0) return b;  if ((t/=d/2)==2) return b+c;  if (!p) p=d*(.3*1.5);
		if (a < Math.abs(c)) { a=c; var s=p/4; }
		else var s = p/(2*Math.PI) * Math.asin (c/a);
		if (t < 1) return -.5*(a*Math.pow(2,10*(t-=1)) * Math.sin( (t*d-s)*(2*Math.PI)/p )) + b;
		return a*Math.pow(2,-10*(t-=1)) * Math.sin( (t*d-s)*(2*Math.PI)/p )*.5 + c + b;
	},
	easeInBack: function (x, t, b, c, d, s) {
		if (s == undefined) s = 1.70158;
		return c*(t/=d)*t*((s+1)*t - s) + b;
	},
	easeOutBack: function (x, t, b, c, d, s) {
		if (s == undefined) s = 1.70158;
		return c*((t=t/d-1)*t*((s+1)*t + s) + 1) + b;
	},
	easeInOutBack: function (x, t, b, c, d, s) {
		if (s == undefined) s = 1.70158; 
		if ((t/=d/2) < 1) return c/2*(t*t*(((s*=(1.525))+1)*t - s)) + b;
		return c/2*((t-=2)*t*(((s*=(1.525))+1)*t + s) + 2) + b;
	},
	easeInBounce: function (x, t, b, c, d) {
		return c - jQuery.easing.easeOutBounce (x, d-t, 0, c, d) + b;
	},
	easeOutBounce: function (x, t, b, c, d) {
		if ((t/=d) < (1/2.75)) {
			return c*(7.5625*t*t) + b;
		} else if (t < (2/2.75)) {
			return c*(7.5625*(t-=(1.5/2.75))*t + .75) + b;
		} else if (t < (2.5/2.75)) {
			return c*(7.5625*(t-=(2.25/2.75))*t + .9375) + b;
		} else {
			return c*(7.5625*(t-=(2.625/2.75))*t + .984375) + b;
		}
	},
	easeInOutBounce: function (x, t, b, c, d) {
		if (t < d/2) return jQuery.easing.easeInBounce (x, t*2, 0, c, d) * .5 + b;
		return jQuery.easing.easeOutBounce (x, t*2-d, 0, c, d) * .5 + c*.5 + b;
	}
});

define("jqueryeasing", ["jquery"], function(){});

define (
'app/modules/DotsNavigation.class',[
	'jquery',
	'hv/util/MathX',
	'app/Helpers',
	'app/Config',
	'app/modules/GATracker',
	'jqueryeasing'
],
function(
	$,
	MathX,
	Helpers,
	Config,
	GATracker
){


	function DotsNavigation( cont ) {
		this.isClicked = false;

		this.cont = cont;

		this.elNo = [];
		this.el;

		this.levelsNo = $( ".level", this.cont).length;

		this.init();

		this.addListeners();

		this.dotsnav = $("#dotsnavigationid");

		this.dotsnav.css({
			'max-height' : $(window).height()
		});

		this.checkIfRouteIsOff();
	}


	DotsNavigation.prototype.setWindowSize = function( w, h ) {
		this.w = w;
		//this.dotsnav.css("left", (this.w-35)+"px" );
	};


	DotsNavigation.prototype.init = function( ) {
		this.$text = $( '.dotsnav' );

		this.el = $( ".element", this.cont );
		this.$links = $('.element a', this.cont);

		var me = this;

		this.cont.on('click', '.level > a', function(e) {
			e.preventDefault();
			me.onElementLvl(this);
		});
		this.cont.on('click', '.element > a', function(e) {
			me.onElement(this);
		});

		var a = $( '.level', this.cont );
		for( var i=0; i<a.length; i++ ) {
			this.elNo[i] = $( 'li', a[i] ).length;
		}
		this.openLevel(-1);

		$(this.cont).on( "mouseleave", function(){ me.isClicked = false; } );
	};


	DotsNavigation.prototype.onElementLvl = function( el ) {
		this.isClicked = false;
		var levelId = $( el ).data("id");

		this.openLevel( levelId );

		$(document).trigger("onclicklvl", [levelId]);
		$(el).trigger('wos-dots-nav-el-click', ['level-' + levelId]);
		if(levelId == 1){
			$(document).trigger("dotsnavigation:goToIntro");
		}else{
			$(document).trigger("dotsnavigation:goTo3dWorld");
		}

		this.isClicked = true;
	};



	DotsNavigation.prototype.onElement = function( el ) {
		this.isClicked = false;
		var href = $( el ).attr('href');
		var afterHash = href.substring(href.indexOf('#')+1);
		$(el).trigger('wos-dots-nav-el-click', [afterHash]);
	};


	DotsNavigation.prototype.openLevel = function( id ) {
		if( this.currentLevel == id ) return;

		if( this.isClicked ) return;

		this.currentLevel = id;

		var $ul = $( ".level > ul", this.cont);
		$ul.parent().css( { "max-height": 14 +"px" } );
		$ul = $ul.filter('[data-id="' + id + '"]');
		$ul.parent().css( { "max-height": (($ul.children().length + 1) * 17+3)+"px" } );
	};


	DotsNavigation.prototype.activate = function( id ) {
		if( this.currentId == id ) return;

		var $link = this.$links.filter('[href="#'+id+'"]');

		if ( $link.length === 0 ) return;

		var $el = $link.parents('.element').eq(0);

		this.el.removeClass("highlighted");

		this.currentId = id;

		$el.addClass("highlighted");

		this.openLevel( $el.parent().data("id") );
	};


	DotsNavigation.prototype.addListeners = function( ) {
		var me = this;
		this.$text.on( "mouseenter", function(){ me.onMouseEnter(); } );
		this.$text.on( "mouseleave", function(){ me.onMouseLeave(); } );

		var $window = $(window);
		$window.on('resize', function() {
			me.dotsnav.css({
				'max-height' : $window.height()
			});
		});
	};
	DotsNavigation.prototype.onMouseEnter = function( ) {
		$(".level").css( { "width": "240px" } );
		//this.dotsnav.css("left", (this.w-35-210)+"px" );
	};
	DotsNavigation.prototype.onMouseLeave = function( ) {
		$(".level").css( { "width": "30px" } );
		//this.dotsnav.css("left", (this.w-35)+"px" );
	};

	DotsNavigation.prototype.checkIfRouteIsOff = function() {
		if( Config.get("isRouteNetworkOff") == "true" )
		{
			this.isRouteOff = true;
		}
		else
		{
			this.isRouteOff = false;
		}
	};


	return DotsNavigation;
});

define(
'app/3d/World3d.class',[
	'jquery',
	'app/3d/Point.class',
	'app/3d/Point3d.class',
	'app/3d/Math3d.class',
	'app/3d/Camera3d.class',
	'app/3d/Elements3d.class',
	'app/3d/Lines3d.class',
	'hv/util/MathX',
	'app/modules/Background2.class',
	'app/modules/DotsNavigation.class',
	'app/Config',
	'app/modules/GATracker'
],
function(
	$,
	Point,
	Point3d,
	Math3d,
	Camera3d,
	Elements3d,
	Lines3d,
	MathX,
	Background2,
	DotsNavigation,
	Config,
	GATracker
){

	var AUTO_SPEED = 7;

	var isAutoPlay = true;
	var isGoingDirectly = false;
	var isStopped = false;
	var isMovingToCurrElement = false; 
	var timerCurrEle = null;

	//var meter = new FPSMeter( $('#dotsnavigationid') );

	var camera3d;

	var bg;
	var math3d;
	var lines3d;
	var elements3d;
	var dotsNavigation;




	function World3d( canvas, context )
	{
		this.elements = [];
		this.elementsData = null;
		this.connections = [];
		this.connectionsData = null;

		this.counter = 0;

		this.c = canvas;
		this.ctx = context;
	}


	World3d.prototype.build = function( elementsData, connectionsData, autoroutesData )
	{
		this.elementsData = elementsData;
		this.connectionsData = connectionsData;
		this.autoroutesData = autoroutesData;

		var me = this;

		math3d = new Math3d();

		camera3d = new Camera3d( math3d, (elementsData.length-1)*Elements3d.EL_Z_DIFF, this.ctx );


		elements3d = new Elements3d( this.elementsData, math3d, camera3d );
		$( elements3d ).bind( "onclick", function( e, el ) {
			me.onElement( el );
		});
		$( elements3d ).bind( "onlvl1linkclick", function( e, el ) {
			me.onLvl1Element3dLinkClick( el );
		});
		$( elements3d ).bind( "onlinkclick", function( e, params ) {
			me.onElement3dLinkClick( params.href, params.pos );
		});

		lines3d = new Lines3d( elements3d.elements, this.elementsData, this.connectionsData, this.autoroutesData, this.ctx, math3d );
		$( lines3d ).bind( "onclick", function( e, targetId ) {
			me.gotoElement( targetId );
		});

		dotsNavigation = new DotsNavigation( $('#dotsnavigationinnerid'), this.elementsData );

		$( document ).bind( "onclickhref", function( e, targetHref ) {
			me.gotoElementHref( targetHref );
		});
		$( document ).bind( "onclicklvl", function( e, targetId ) {
			var elID = me.gotoLvl( targetId );

			lines3d.dehighlightRoute();
		});

		this.fourthLevelPos = this.getFourthLayerZ();
		bg = new Background2( this.fourthLevelPos );

		if( Config.get("isRouteNetworkOff") == "true" )
		{
			this.isRouteOff = true;
			camera3d.setMaxZPos( this.getFourthLayerZ()-5000 );
		}
		else
		{
			this.isRouteOff = false;
			camera3d.setMaxZPos( elements3d.getMaxZPos() );
		}

		var startPos = elements3d.getElementPos(0);

		if( Config.get("isRouteNetworkOff") == "true" )
		{
			this.autoplayEndPos = elements3d.getMaxZPos();
		}
		else
		{
			this.autoplayEndPos = -elements3d.elements[ elements3d.getLevelFirstElement(4) ].position.z || 20000;
		}

		camera3d.setPosition( startPos.x, startPos.y, startPos.z-4000);


		this.elements3d = elements3d;
		this.camera3d = camera3d;
		this.lines3d = lines3d;
	};



	World3d.prototype.onEF = function()
	{
		camera3d.countNextPos();

		//meter.tick();

		this.findCurrentCameraPos();

		if( bg && camera3d.position.z < this.fourthLevelPos )
		{
			this.setBgPos();
		}

		if(isAutoPlay && camera3d.position.z < this.autoplayEndPos) {
			camera3d.move(0,0, AUTO_SPEED);
		}

		if( isStopped ) return;

		this.redraw();


	};


	World3d.prototype.setBgPos = function()
	{
		var level = elements3d.closest ? elements3d.closest.data.level : 0;

		bg.setPos( camera3d.position.x, camera3d.position.y, camera3d.position.z, level );
	};


	World3d.prototype.stop = function()
	{
		isStopped = true;
	};
	World3d.prototype.play = function()
	{
		isStopped = false;
	};

	World3d.prototype.show = function()
	{
		$("#world3dcontid").css({"display":"block"});
	};

	World3d.prototype.hide = function()
	{
		$("#world3dcontid").css({"display":"none"});
	};



	World3d.prototype.isRunning = function(){
		return !isStopped;
	};

	World3d.prototype.isPaused = function()
	{
		return !isAutoPlay;
	};
	World3d.prototype.pause = function()
	{
		isAutoPlay = false;
	};
	World3d.prototype.unpause = function()
	{
		isAutoPlay = true;
		isGoingDirectly = false;
	};


	World3d.prototype.moveCamera = function( x, y, z )
	{
		camera3d.move( x, y, z );
		isGoingDirectly = false;
		var closestElement = elements3d.closest;
		if( lines3d.isRouteHighlighted && currentEl != closestElement.index )
		{
			lines3d.dehighlightRoute();
		}

	};

	World3d.prototype.setPositionDif = function( pX, pY )
	{
		camera3d.setPositionDif( pX, pY );
		bg.setPositionDif( pX, pY );
	};


	World3d.prototype.redraw = function()
	{
		this.counter = ++this.counter%3;

		this.clear();

		var e = elements3d.closest;
		$('.linescanvascont').css({transform: 'translateZ('+(e.zindex - 1)+'px)'});
		lines3d.renderConnections( elements3d.closest.index, elements3d.isClosestVisible());
		$(document).trigger('world3d:currentElement',{level: e.data.level, id: e.data.id, visible:elements3d.isClosestVisible()});
		elements3d.render( this.counter );

		if(elements3d.closest.index === currentEl && isMovingToCurrElement){
			isMovingToCurrElement = false;
			clearTimeout(timerCurrEle);
			timerCurrEle = setTimeout(function(){
				$(document).trigger('world3d:finishedTransitionCurrElement');
			},2000);
		}
	};


	World3d.prototype.clear = function()
	{
		this.ctx.clearRect(0, 0, this.c.width, this.c.height);
	};


	World3d.prototype.setCenter = function( x, y )
	{
		math3d.setCenter( x, y );
	};

	World3d.prototype.setWindowSize = function( w, h )
	{
		math3d.setWindowSize( w, h );

		if( dotsNavigation )
		{
			dotsNavigation.setWindowSize( w, h );
		}
	};


	World3d.prototype.onElement = function( el )
	{
		//checks if clicked element is the current element and if it's close enough to the camera position
		//if( currentEl == el.index && Math.abs(el.getPosition().z+this.getCameraPos().z)<500)
		if( Math.abs(el.getPosition().z+this.getCameraPos().z)<2000)
		{
			if( el.data.level == '1' )
			{
				this.onLvl1Element3dLinkClick( el.index );
			}
			else
			{
				elements3d.onAnchor( el );
			}
		}
		else
		{
			this.gotoElement( el.index );
		}
	};

	World3d.prototype.onLvl1Element3dLinkClick = function( id )
	{
		lines3d.dehighlightRoute();
		lines3d.highlightRoute( this.autoroutesData[parseInt(id, 10)]);
		this.gotoElementHref( this.autoroutesData[parseInt(id, 10)][1] );

	};

	World3d.prototype.onElement3dLinkClick = function( href, pos )
	{
		$(this.c).trigger("onElement3dLinkClick", { href:href, pos:pos } );
	};

	World3d.prototype.hideLoader = function( href )
	{
		elements3d.hideLoader();
	};

	var currentEl = -1;
	World3d.prototype.gotoPrev = function()
	{
		this.gotoBy(-1);
	};

	World3d.prototype.gotoNext = function()
	{
		this.gotoBy(1);
	};
	World3d.prototype.gotoBy = function(d)
	{
		elements3d.findClosest();
		var target = elements3d.closest.index;
		do{
			target += d;
		} while (
			target >= 0
			&& target <= this.elementsData.length-1
			&& elements3d.elements[target].invisible
		);

		target = Math.min( target, this.elementsData.length-1 );
		target = Math.max( target, 0 );

		this.gotoElement(target);
		lines3d.dehighlightRoute();
	};
	World3d.prototype.gotoElement = function( id )
	{
		currentEl = id;
		var element = elements3d.elements[ currentEl ];
		GATracker.replaceLocation('#' + element.id, 'Element', true);

		return this.gotoCurrent();
	};
	World3d.prototype.gotoElementHref = function( href )
	{
		var index = this.findElementIdByHref( href );
		return this.gotoElement( index );
	};
	World3d.prototype.gotoLvl = function( id )
	{
		var elementIndex = elements3d.getLevelFirstElement(id);
		var element = elements3d.elements[ elementIndex ];
		this.gotoElementHref( '#' + element.id );
		return  '#' + element.id;
	};
	World3d.prototype.gotoCurrent = function()
	{
		var el = elements3d.elements[ currentEl ],
			p = el.getPosition();


		camera3d.setTargetXY( p.x, -p.y );
		camera3d.setTargetZ( -p.z );
		camera3d.isGoingDirectly = true;
		isMovingToCurrElement = true;
		isGoingDirectly = true;

		this.pause();

		if( this.elementsData[currentEl].level == '4' )
		{
			$(this).trigger("onlevelfour", [+currentEl-parseInt(elements3d.getLevelFirstElement("4"),10)] );
		}

		return el.id;
	};

	World3d.prototype.findElementIdByHref = function( href )
	{
		if( href.indexOf('#') === 0 )
		{
			href = href.slice(1);
		}

		for( var i=0; i<this.elementsData.length; i++ )
		{
			if( this.elementsData[i].id == href )
			{
				return i;
			}
		}
		return -1;
	};

	World3d.prototype.findCurrentCameraPos = function()
	{
		//
		// Finds camera position on a straight line between two closest elements.
		//
		elements3d.findClosest();

		var closestElement = elements3d.closest;
		var secondClosestElement = elements3d.secondClosest;

		var p1 = closestElement.getPosition();
		var p2 = secondClosestElement.getPosition();

		camera3d.findCurrentCameraPos( p1, p2 );


		closestElement = elements3d.findClosestElement(function(e){
			return !e.invisible;
		});

		dotsNavigation.activate( closestElement.id );

		if( isGoingDirectly )
		{
			dotsNavigation.openLevel(this.elementsData[currentEl].level);
		}

		if( elements3d.closest.index == currentEl )
		{
			if( lines3d.isRouteHighlighted && isGoingDirectly)
			{
				this.autoOpen();
			}
			isGoingDirectly = false;
		}
	};

	World3d.prototype.autoOpen = function()
	{
		var lvl = parseInt(this.elementsData[currentEl].level);
		if( lvl > 1 && lvl < 4 )
		{
			var href = elements3d.getElementHref( currentEl );

			var me = this;
			setTimeout( function(){ me.onElement3dLinkClick( href, elements3d.getLoaderPosition( currentEl ) ); }, 1200);
		}
	}

	World3d.prototype.getCameraPos = function()
	{
		return camera3d.position;
	};

	World3d.prototype.getFourthLayerZ = function()
	{
		return elements3d.getFourthLayerZ();
	};

	return World3d;
});

define(
	'app/routenetwork/SmoothNetworkMap.class',['jquery', 'hv/util/MathX', 'app/3d/Point.class', 'app/Helpers'],
	function($, MathX, Point, Helpers ){

	var ZOOMGAP = 4.5; // the scale difference between the different zoom levels


	var mapSize = [ { w:2560, h:1720 }, { w:2560, h:1720 }, { w:2560, h:1720 } ];

	var zoomTypes = ["cover", "cover", "cover"];

	var zooms = [ 1, ZOOMGAP, ZOOMGAP * ZOOMGAP ];
	var zoomsPositions = [ { x:0, y:0 }, { x:1002, y:604 }, { x:1224, y:751 } ];


	var windowW, windowH;

	var loaded = 0;
	var containers = [];
	var containersPos = [];

	var isInited = false;

	var images = [];



	function SmoothNetworkMap()
	{
		this.cont = $( ".routenetworkmapimgcont" );
		var c = $( ".routenetworkmapimgcont" );
		containers = [ $( c[0] ), $( c[1] ), $( c[2] ) ];

		images.push( $( ".routenetworkmapimg", containers[0] )[0] );
		images.push( $( ".routenetworkmapimg", containers[1] )[0] );
		images.push( $( ".routenetworkmapimg", containers[2] )[0] );

		isInited = true;
		this.resize( $( window ).width(), $( window ).height() );
	}


	SmoothNetworkMap.prototype.resize = function( w, h )
	{
		windowW = w;
		windowH = h;

		this.rescale(0);
		this.rescale(1);
		this.rescale(2);
	};


	SmoothNetworkMap.prototype.getIsInited = function()
	{
		return isInited;
	};


	SmoothNetworkMap.prototype.setPosition = function( norm )
	{
		var a = 2+ 8*norm;

		var n = 1 - norm;
		var s = ( n * n )* (ZOOMGAP * ZOOMGAP - 1) / ZOOMGAP + 1/ZOOMGAP;

		this.setAlpha( a.toFixed(5) );
		this.setBackgroundScale( s, n * n, n );
	}


	SmoothNetworkMap.prototype.setAlpha = function( a )
	{
		a = Math.min(1, Math.max(0,a));
		if(this.currentA != a)
		{
			this.currentA = a;
			this.cont.css({ 'opacity':Number(a).toFixed(15) });
		}
	};

	SmoothNetworkMap.prototype.setBackgroundScale = function( scale, norm, n )
	{
		if( !isInited ) return;

		var scale = MathX.range( scale, 1/ZOOMGAP, 100 );

		this.currentSmoothScale = scale;
		this.mapScale = this.currentSmoothScale*containersPos[0].scale*ZOOMGAP;

		var x0 = 0, y0 = 0, x1 = 0, y1 = 0, x2 = 0, y2 = 0;

		var s = 2*(norm-0.5);

		this.containerX = x0;
		this.containerY = y0;




		this.scaleBkgnd( images[0], x0, y0, scale*ZOOMGAP );
		this.scaleBkgnd( images[1], x1, y1, scale );
		this.scaleBkgnd( images[2], x2, y2, scale/ZOOMGAP );

		if(n<0) images[1].style.visibility = 'hidden';

	};


	SmoothNetworkMap.prototype.scaleBkgnd = function(bg, x, y, scale) {
		Helpers.translate( bg, x, y, 0, 0, scale );
		var visibility = scale * ZOOMGAP < 1.25;
		bg.style.display = visibility ? 'none' : 'block';
		bg.style.visibility = visibility ? 'hidden' : 'visible';
	};


	SmoothNetworkMap.prototype.getScale = function()
	{
		return this.mapScale || 1;
	};


	SmoothNetworkMap.prototype.getContPos = function(scale)
	{
		if ( !scale ) {
			scale = this.mapScale;
		}
		var px = (scale * mapSize[0].w - windowW) / 2 - this.containerX;
		var py = (scale * mapSize[0].h - windowH) / 2 - this.containerY;

		return new Point(px, py);
	};


	SmoothNetworkMap.prototype.rescale = function(id)
	{
		var posX=0, posY=0;
		var mapW, mapH, scale=1;

		var pW = windowW/mapSize[ id ].w;
		var pH = windowH/mapSize[ id ].h;

		if( zoomTypes[id] == "cover" )
		{
			if( pW <= pH )
			{
				mapH = windowH;
				scale = pH;
				mapW = mapSize[ id ].w * scale;
			}
			else
			{
				mapW = windowW;
				scale = pW;
				mapH = mapSize[ id ].h * scale;
			}
		}
		else
		{
			if( pW >= pH )
			{
				mapH = windowH;
				scale = pH;
				mapW = mapSize[ id ].w * scale;
			}
			else
			{
				mapW = windowW;
				scale = pW;
				mapH = mapSize[ id ].h * scale;
			}
		}

		posX = ( windowW - mapW ) / 2;
		posY = ( windowH - mapH ) / 2;

		containersPos[id] = { x:posX, y:posY, scale:scale, w:mapW, h:mapH };

		containers[id].css( { "width": mapW+"px ", "height": mapH+"px" } );
		containers[id].css( { "left": posX+"px ", "top": posY+"px" } );
	};

	return SmoothNetworkMap;
});

define('hv/browser/Window',['jquery'],function($){

	var $w = $(window), windowWidth, windowHeight, scrollTop, scrollLeft;


	function recalc(){
		windowWidth = $w.width();
		windowHeight = $w.height();
	}

	function scroll(){
		scrollTop = $w.scrollTop();
		scrollLeft = $w.scrollLeft();
	}

	$w.resize(recalc);
	$w.scroll(scroll);
	recalc();
	scroll();

	var Window = {
		width: function() {
			return windowWidth;
		},
		height: function() {
			return windowHeight;
		},
		scrollTop: function() {
			return scrollTop;
		},
		scrollLeft: function() {
			return scrollLeft;
		},
		resize: function(){ $w.resize.apply($w, arguments); }
	};

	return Window;
});

define(
	'app/modules/Tooltip.class',['jquery', 'hv/util/MathX', 'hv/browser/Window', 'jqueryeasing'],
	function($, MathX, Window) {

	var TRIANGLE_SIZE = 13;
	var MARGIN = 10;

	var ANIM_DIFF = 14;

	function Tooltip(container, html, posType) {
		this.xpos;
		this.ypos;
		this.type;
		this.container = container;
		this.$triggerEl = container.closest('.airport, .iconplane');
		this.html = html;
		this.isInited = false;

		this.positioningType = "TB";
		if (posType) {
			this.positioningType = posType;
		}
	}


	Tooltip.prototype.init = function() {
		if (this.isInited === false) {
			this.isInited = true;
			this.container.append(this.html);
		}
	};

	Tooltip.prototype.show = function() {
		var wasHidden = this.container.css("visibility") == "hidden";


		this.container.addClass('is-visible');


		if (wasHidden) {
			this.init();
			this.checkPosition();

		}


		this.container.find('img').on('load', function(e) {
			$(this).addClass('is-loaded');
		});

		if ( this.container.css('position') == 'fixed' ) {
			$('body').append(this.container);
		}
	};


	Tooltip.prototype.checkPosition = function() {
		this.w = $(".tooltip", this.container).width();
		this.h = $(".tooltip", this.container).height();

		if (this.positioningType == "RL") {
			this.positionRightLeft();
		} else {
			this.positionTopBottom();
		}
	};


	Tooltip.prototype.hide = function() {

		this.container.removeClass('is-visible');
	};


	Tooltip.prototype.moveWithmouse = function() {
		var me = this;
		$(window).mousemove(function(event) {
			me.updatePosition(event.pageX, event.pageY);
		});
	};


	Tooltip.prototype.resize = function(windowW, windowH) {
	};

	Tooltip.prototype.updatePosition = function(x, y) {
		this.xpos = x;
		this.ypos = y;
	};

	Tooltip.prototype.positionTopBottom = function() {
		var x = this.xpos;
		var y = this.ypos;

		var posX = this.w / 2 * -1,
			posY = (this.h * -1) - 40,
			marginTop = this.$triggerEl.offset().top,
			marginLeft = this.$triggerEl.offset().left - posX,
			marginBottom = Window.height() - marginTop,
			marginRight = Window.width() - marginLeft,
			triggerPosY = marginTop,
			triggerPosX = this.$triggerEl.offset().left;

		//vertical position
		if((triggerPosY + posY) > MARGIN || marginTop > marginBottom){	// on top
			this.type = "top";

			this.container.removeClass('tooltip--bottom').addClass('tooltip--top');
			this.addClass("tooltipposition-top");
		} else { //on bottom
			this.type = "bottom";

			this.container.removeClass('tooltip--top').addClass('tooltip--bottom');
			posY = 40;
			this.addClass("tooltipposition-bottom");
		}

		//horizontal position
		//position if element is on left edge
		if(triggerPosX - Math.abs(posX) < MARGIN) {
			if(triggerPosX > 30) {
				posX = (marginLeft - Math.abs(posX) - MARGIN) * -1;
			} else {
				posX = -20;
			}

			this.container.find('.tooltiptriangle').css({
				'left' : posX * -1
			});

			setTransformOrigin(this.container);
		} else if(marginRight < MARGIN) { // right edge
			if(triggerPosX < Window.width() - 30) {
				posX = (marginRight - Math.abs(posX) - MARGIN);
			} else {
				posX = (marginRight - Math.abs(posX) + 20);
			}

			this.container.find('.tooltiptriangle').css({
				'left' : posX * -1
			});

			setTransformOrigin(this.container);
		} else {
			this.container.find('.tooltiptriangle').css({
				'left' : ''
			});
		}

		function setTransformOrigin(container) {
			if(container.hasClass('tooltip--bottom')) {
				container.css({
					'transform-origin' : ((posX * -1) / container.outerWidth() * 100) +'% top'
				});
			} else {
				container.css({
					'transform-origin' : ((posX * -1) / container.outerWidth() * 100) +'% bottom'
				});
			}
		}

		this.setPosition(posX, posY);
	};


	Tooltip.prototype.positionRightLeft = function() {
	};


	Tooltip.prototype.setPosition = function(pX, pY) {
		this.container.css({
			'left': Math.round(pX),
			'top': Math.round(pY)
		});
	};

	Tooltip.prototype.setPositionTriangle = function(pX, pY) {
		$(".tooltiptriangle", this.container).css({
			'left': pX,
			'top': pY
		});
	};

	Tooltip.prototype.addClass = function(c) {
		var e = $(".tooltiptriangle", this.container);

		e.removeClass("tooltipposition-left");
		e.removeClass("tooltipposition-right");
		e.removeClass("tooltipposition-top");
		e.removeClass("tooltipposition-bottom");

		e.addClass(c);
	};

	return Tooltip;
});

define('hv/util/MicroTemplate',[], function(){

	// Based on:
	// Simple JavaScript Templating
	// John Resig - http://ejohn.org/ - MIT Licensed
	// http://ejohn.org/blog/javascript-micro-templating
	// 
	// Hinderling Volkart AG, Severin Klaus

	function convertToJavascript(str){
		var converted = str
			.replace(/[\r\t\n]/g, " ")
			.split("[%").join("\t")
			.replace(/((^|%])[^\t]*)'/g, "$1\r")
			.replace(/\t=(.*?)%]/g, "',$1,'")
			.split("\t").join("');")
			.split("%]").join("p.push('")
			.split("\r").join("\\'");

		var code = "var p=[],print=function(){p.push.apply(p,arguments);};" +

			// Introduce the data as local variables using with(){}
			"with(obj){p.push('" +

			// Convert the template into pure JavaScript
			converted + "');}return p.join('');";

		return new Function('obj', code);
	}


	var MicroTemplate = {
		convert: convertToJavascript
	};

	return MicroTemplate;

});

define(
	'app/routenetwork/Airport.class',['jquery', 'app/3d/Point.class', 'app/modules/Tooltip.class', 'app/Helpers', 'hv/util/MicroTemplate', 'jqueryeasing'],
	function($, Point, Tooltip, Helpers, MicroTemplate) {


	var getTooltip = MicroTemplate.convert($('#template-tooltip-airport').val());

	function Airport(element, data) {
		var self = this;

		this.element = $(element);
		this.data = data;

		this.isHidden = false;

		this.position = new Point();

		this.$tt = $(".tooltipcont", this.element);
		var ttdata = this.$tt.data('tooltip');

		var html = getTooltip(ttdata);

		this.iconcont = $(".icon", this.element); //.hide();
		this.tooltip = new Tooltip(this.$tt, html);


		this.$tt.on('click', '.closebutton', function(event){
			event.preventDefault();
			self.hideTooltip();
		});

		this.addMouseHandlers();
		this.hide();
	}

	Airport.prototype.addMouseHandlers = function() {
		var me = this;
		this.$tt.on('click', '.tooltiplink.internal', function(e) {
			me.hideTooltip();
			$(this).trigger('wos-routenetwork-tooltiplink-int-click');
		});
		this.$tt.on('click', '.tooltiplink.external', function(e) {
			$(this).trigger('wos-routenetwork-tooltiplink-ext-click');
		});
	};

	Airport.prototype.showTooltip = function() {
		this.element.css('display', '');

		this.tooltipOpened = true;
		this.setPosition(
			Math.round(this.position.x),
			Math.round(this.position.y),
			this.wW,
			this.wH
		);
		this.place();

		this.tooltip.resize(this.wW, this.wH);
		this.tooltip.updatePosition(this.position.x, this.position.y);

		this.element.removeClass('is-hover');
		this.element.addClass('is-active');
		this.tooltip.show();

		$(this).trigger('wos-routenetwork-airport-click');
		$(this).trigger("ontooltipopen");

		this.element.css({
			"z-index": 4000
		});
	};

	Airport.prototype.hideTooltip = function() {
		var me = this;
		setTimeout(function(){
			me.element.css('display', 'none');

			me.tooltipOpened = false;

			me.element.removeClass('is-active');

			me.tooltip.hide();

			$(me).trigger("ontooltipclose");

			me.element.css({
				"z-index": ''
			});

			me.element.hide();
		},10);
	};

	Airport.prototype.setPosition = function(x, y, wW, wH) {
		this.position.x = x;
		this.position.y = y;

		this.wW = wW;
		this.wH = wH;
	};

	Airport.prototype.show = function( labelVisible ) {
		var el = this.element;
		if (this.isHidden) {
			this.isHidden = false;
			el.css({
				'display':''
			});
			setTimeout(function(){
				el.addClass('is-hover');
			},0);

		}
		var $label = el.children('.hotspot-tooltip');
		if ( !$label.length ) {
			var data = el.find('.tooltipcont').data('tooltip');
			var temperature = "";
			if(data.temperature){
				temperature = " <span class='weather-temperature'>"+data.temperature+"</span><span class='weather-icon "+data.temperatureicon+"'></span>";
			}
			
			$label = $('<div class="hotspot-tooltip"><div class="hotspot-tooltip__inner">'+ data.title + temperature +'</div><div class="hotspot-tooltip__arrow hotspot-tooltip__arrow--bottom"></div></div>');
			el.append($label);
		}
		$label.css('display', labelVisible ? '' : 'none');
		if ( labelVisible ) {
			this.positionTooltipLabel($label);
			$label.addClass('is-visible');
		} else {
			$label.removeClass('is-visible');
		}
	};

	Airport.prototype.positionTooltipLabel = function($tooltip) {
		var $tooltipArrow = $tooltip.find('.hotspot-tooltip__arrow'),
			$tooltipInner = $tooltip.find('.hotspot-tooltip__inner');

		if(this.element.offset().top > 100) { //position it on top
			$tooltip.css({
				'top': '-80px',
				'left': 0
			});
			$tooltipArrow.removeClass('hotspot-tooltip__arrow--top').addClass('hotspot-tooltip__arrow--bottom');
		} else {
			$tooltip.css({
				'top': '40px',
				'left': 0
			});
			$tooltipArrow.removeClass('hotspot-tooltip__arrow--bottom').addClass('hotspot-tooltip__arrow--top');
		}

		$tooltip.css({
			'left': - ($tooltip.outerWidth() / 2)
		});
		$tooltipArrow.css({
			'left': ($tooltip.outerWidth() / 2) - ($tooltipArrow.outerWidth() / 2)
		});
	};


	Airport.prototype.hide = function() {
		if (!this.isHidden) {
			this.isHidden = true;
			this.element.css({
				'display' : 'none'
			});
			this.element.removeClass('is-hover');
		}
	};

	Airport.prototype.place = function() {
		if (this.position.x < -10 || this.position.x > this.wW + 10 || this.position.y < -10 || this.position.y > this.wH + 10) {
			this.hide();
		} else {
			this.show();

			Helpers.translate(this.element[0], this.position.x, this.position.y);
		}
		if( this.tooltipOpened )
		{
			this.tooltip.resize(this.wW, this.wH);
			this.tooltip.updatePosition(this.position.x, this.position.y);
			this.tooltip.checkPosition();
		}
	};


	return Airport;
});

define(
	'app/routenetwork/Airplane.class',['jquery', 'app/3d/Point.class', 'app/modules/Tooltip.class', 'app/Helpers', 'hv/util/MicroTemplate'],
	function($, Point, Tooltip, Helpers, MicroTemplate) {



	


	function Airplane(element, data, id) {
		var self = this;

		this.element = $(element);
		this.data = data;
		this.id = id;

		this.isHidden = false;

		this.position = new Point();
		this.tooltip;

		this.iconcont = $(".icon", this.element);
		var $tt = $(".tooltipcont", this.element);
		var ttdata = $tt.data('tooltip');

		var getTooltip = MicroTemplate.convert($('#template-tooltip-airplane').val());

		try {
			var html = getTooltip(ttdata);
		} catch(e){
			var html = 'Nothing';
		}
		this.tooltip = new Tooltip($tt, html);

		$tt.on('click', '.closebutton', function(event){
			event.preventDefault();
			self.hideTooltip();
		});
		this.$tt = $tt;

		this.addMouseHandlers();
		this.hide();
	}

	Airplane.prototype.addMouseHandlers = function() {
		var me = this;

		this.$tt.on('click', '.tooltiplink.internal', function(e) {
			me.hideTooltip();
			$(this).trigger('wos-routenetwork-tooltiplink-int-click');
		});
		this.$tt.on('click', '.tooltiplink.external', function(e) {
			$(this).trigger('wos-routenetwork-tooltiplink-ext-click');
		});
	};


	Airplane.prototype.showTooltip = function() {
		this.tooltipOpened = true;

		this.tooltip.resize(this.wW, this.wH);
		this.tooltip.updatePosition(this.position.x, this.position.y);

		this.element.removeClass('is-hover');
		this.element.addClass('is-active');
		this.tooltip.show();


		$(this).trigger('wos-routenetwork-airplane-click');
		$(this).trigger("ontooltipopen");

		this.element.show();
		this.element.css({
			"z-index": 4000
		});
	};

	Airplane.prototype.hideTooltip = function() {
		var me = this;
		setTimeout(function(){
			if ( !me.element ) {
				return;
			}

			me.tooltipOpened = false;

			me.element.removeClass('is-active');
			me.tooltip.hide();

			$(me).trigger("ontooltipclose");
			me.element.css({
				"z-index": ''
			});

			me.element.hide();
		}, 10);
	};

	Airplane.prototype.setPosition = function(x, y, wW, wH) {
		this.position.x = x;
		this.position.y = y;

		this.wW = wW;
		this.wH = wH;
	};

	Airplane.prototype.setPositionBezier = function(x, y, a) {
		if ( x === null ) {
			this.bezierPos = null;
			return;
		}

		this.bezierPos = {
			x: x,
			y: y,
			a: a
		};
	};

	Airplane.prototype.getPositionBezier = function() {
		return this.bezierPos;
	};

	Airplane.prototype.show = function(labelVisible) {
		var el = this.element;

		if (this.isHidden) {
			this.isHidden = false;
			el.css({
				'visibility': 'visible',
				'display':''
			});
		}
		setTimeout(function(){
			el.addClass('is-hover');
		},0);
		var $label = el.children('.hotspot-tooltip');
		if ( !$label.length ) {
			var data = el.find('.tooltipcont').data('tooltip');
			$label = $('<div class="hotspot-tooltip"><div class="hotspot-tooltip__inner"><span class="icon-winglet"></span>'+ data.no +'</div><div class="hotspot-tooltip__arrow hotspot-tooltip__arrow--bottom"></div></div>');
			el.append($label);
		}
		$label.css('display', labelVisible ? '' : 'none');
		if ( labelVisible ) {
			this.positionTooltipLabel($label);
			$label.addClass('is-visible');
		} else {
			$label.removeClass('is-visible');
		}
	};

	Airplane.prototype.positionTooltipLabel = function($tooltip) {
		var $tooltipArrow = $tooltip.find('.hotspot-tooltip__arrow'),
			$tooltipInner = $tooltip.find('.hotspot-tooltip__inner');

		if(this.element.offset().top > 100) { //position it on top
			$tooltip.css({
				'top': '-80px',
				'left': 0
			});
			$tooltipArrow.removeClass('hotspot-tooltip__arrow--top').addClass('hotspot-tooltip__arrow--bottom');
		} else {
			$tooltip.css({
				'top': '40px',
				'left': 0
			});
			$tooltipArrow.removeClass('hotspot-tooltip__arrow--bottom').addClass('hotspot-tooltip__arrow--top');
		}

		$tooltip.css({
			'left': - ($tooltip.outerWidth() / 2)
		});
		$tooltipArrow.css({
			'left': ($tooltip.outerWidth() / 2) - ($tooltipArrow.outerWidth() / 2)
		});
	};

	Airplane.prototype.hide = function() {
		if (!this.isHidden) {
			this.isHidden = true;
			this.element.css({
				'visibility': 'hidden',
				'display' : 'none'
			});
			this.element.removeClass('is-hover');
		}
	};

	// translate( elem, x, y, z, r, s, a, zindex, omit3d )

	Airplane.prototype.place = function(rotation, scale) {
		if (this.position.x < -10 || this.position.x > this.wW + 10 || this.position.y < -10 || this.position.y > this.wH + 10) {
			this.hide();
		} else {
			this.show();
			if(this.tooltipOpened) {
				Helpers.translate(this.element[0], Math.round(this.position.x), Math.round(this.position.y));
			} else {
				Helpers.translate(this.element[0], this.position.x, this.position.y);
			}
		}
		Helpers.translate(this.iconcont[0], 0, 0, 0, rotation, scale, 1, 0, true);
		if( this.tooltipOpened == true )
		{
			this.tooltip.resize(this.wW, this.wH);
			this.tooltip.updatePosition(this.position.x, this.position.y);
			this.tooltip.checkPosition();
		}
	};

	Airplane.prototype.remove = function(){
		if ( this.tooltipOpened ) {
			this.hideTooltip();
		}
		this.element.remove();
		this.element = null;
		this.iconcont = null;
		this.tooltip = null;
	};

	Airplane.prototype.getId = function() {
		return this.id;
	};

	Airplane.prototype.getData = function() {
		return this.data;
	};

	return Airplane;
});

define(
	'app/routenetwork/WatchUpdater.class',['jquery'],
	function( $ ){



	function WatchUpdater() {
		this.timer = setInterval(this.updateTime.bind(this), 1000);

		this.$t = $( ".js-current-time" );
	}

	WatchUpdater.prototype.update = function(str)
	{
		this.$t.text( str );
	};

	WatchUpdater.prototype.updateTime = function() {
	 	this.$t.html(new Date().toTimeString().replace(/.*(\d{2}:\d{2}:\d{2}).*/, "$1"))
	};

	return WatchUpdater;

});

 define(
	'app/routenetwork/SmoothRouteNetwork.class',['jquery', 'app/Config', 'hv/util/MathX', 'app/3d/Point.class', 'app/routenetwork/SmoothNetworkMap.class', 'app/routenetwork/Airport.class', 'app/routenetwork/Airplane.class', 'app/routenetwork/WatchUpdater.class', 'app/3d/Elements3d.class', 'app/Helpers'],
	function($, Config, MathX, Point, SmoothNetworkMap, Airport, Airplane, WatchUpdater, Elements3d, Helpers ){

	var width, height;

	var airports = [];
	var airportsEl = [];

	var connections = [];
	var planes = [];
	var planesEl = [];

	var networkmap;
	var isTouch = isTouchDevice();

	var connectionCounter = 0;


	var airportImage = new Image();
	airportImage.src = Config.get('imgPathIconAirport');
	var planeImage = new Image();
	planeImage.src = Config.get('imgPathIconPlane');

	function isTouchDevice() {
  		return !!('ontouchstart' in window);
	}

	function SmoothRouteNetwork( canvas, context )
	{
		var self = this;

		this.$html = $('html');

		this.$canvas = $(canvas);

		this.c = canvas;
		this.ctx = context;

		this.cl = document.getElementById('routenetworklinesid');
		this.cltx = this.cl.getContext("2d");

		this.cont = $('#routenetworkelements');

		this.airportsCont = $( '#airportscontid' );
		this.connectionsCont =  $( '#connectionscontid' );

		this.zDiff = Elements3d.EL_Z_DIFF_LVL4;

		this.isChanging = false;


		this.parseAirports();
		this.parseConnections();

		this.build();


		$("#routenetworkelementsbackgroundid").hide();
		$("#routenetworkelementsbackgroundid").css({"z-index":""});

		var me = this;
		$("#routenetworkelementsbackgroundid").click( function(event) {
			event.stopPropagation();
			me.onBgClick();
		});

		if ( !isTouch ) {
			this.cont.on('mousemove', function(event){
				var canvasOffset = self.$canvas.offset();

				var x = event.clientX - canvasOffset.left;
				var y = event.clientY - canvasOffset.top;

				me.checkMouseMove(x, y);
			});
		}

		this.cont.on('click', function(event){
			var canvasOffset = self.$canvas.offset();

			var x = event.clientX - canvasOffset.left;
			var y = event.clientY - canvasOffset.top;

			me.checkClick(x, y);
		});


		$(window).on('keydown', function(e) {
			if(e.keyCode === 27) {
				me.onBgClick();
			}
		});

		this.watchUpdater = new WatchUpdater();

	}


	//
	//	HTML PARSING
	//
	SmoothRouteNetwork.prototype.parseAirports = function()
	{
		airports = [];
		var a = $( ".airport", "#airportscontid");

		for( var i = 0; i<a.length; i++ )
		{
			var airport = $( a[i] );
			var code = airport.data("code");
			var posx = airport.data("posx");
			var posy = airport.data("posy");

			airports.push( { code:code, position:{ x:posx, y:posy } } );
		}
	};

	SmoothRouteNetwork.prototype.parseConnections = function()
	{
		connections = [];

		var a = $( ".iconplane", "#connectionscontid");

		for( var i = 0; i<a.length; i++ )
		{
			var connection = $( a[i] );
			var from = connection.data("from");
			var to = connection.data("to");
			var position = connection.data("position");
			var code = connection.data("code");

			connections.push( { from:from, to:to, position:position, code:code } );
		}
	};




	// UPDATE VIA JSON

	SmoothRouteNetwork.prototype.update = function(){
		// console.log('Updating Route Network ...');

		var self = this;
		var url = Config.get('routeNetworkUpdate');
		if ( !url ) {
			// console.log("- could not update. URL is missing.");
			return;
		}

		$.getJSON(url, function(data){
			self.updateData(data);
		}).fail(function(){
			// console.log('- failed');
		});

	};

	SmoothRouteNetwork.prototype.updateData = function(data){
		var i, pos, flight, plane, planeHash = {}, flightHash = {};
		var stats = { moved: 0, added: 0, removed: 0 };

		for (i = 0; i < planes.length; i++) {
			plane = planesEl[i];
			planeHash[ plane.tooltip.container.data('tooltip').no ] = planes[i];
		}

		var len = data.flights.length, id;
		for (i = 0; i < len; i++) {
		// for (i = len-1; i >= 0; i--) {
			flight = data.flights[i];
			id = flight['no']
			flightHash[id] = flight;
			plane = planeHash[id];
			if ( plane ) {
				pos = Number(plane.pos);
				plane.pos = Number(flight.position);
				if ( pos != plane.pos ) {
					stats.moved++;
					// value has changed: reset position bezier to force recalculation
					plane.el.css('transition','-webkit-transform 500ms ease-in-out');
					plane.flaggedForUpdate = true;
				}

			} else {
				// add missing plane
				stats.added++;
				this.addConnectionElement(flight);
			}
		}

		// remove planes that are no more available
		for (i in planeHash) {
			if ( !flightHash[i] ) {
				// remove flight
				stats.removed++;
				plane = planeHash[i];
				plane.flaggedForDelete = true;
			}
		}
		for (i=planes.length - 1; i >= 0; i-- ) {
			plane = planes[i];
			if ( plane.flaggedForDelete ) {
				planes.splice( i, 1 );
				plane = planesEl.splice( i, 1 );

				plane[0].remove();

			} else
			if ( plane.flaggedForUpdate ) {
				plane.flaggedForUpdate = false;
				planesEl[i].setPositionBezier(null);
			}
		}

		// console.log('- updated. Added: '+stats.added+', removed: '+stats.removed+', updated: '+stats.moved);

		this.clear();
		this.render({ forceBezier: true });
	};

	SmoothRouteNetwork.prototype.addConnectionElement = function(data){
		var $el = $('<div class="iconplane"><div class="icon"></div></div>');
		$el.data('from', data.from.code)
		$el.data('to', data.to.code)
		$el.data('position', data.position);

		var $tooltip = $('<div class="tooltipcont"></div>');
		$tooltip.data('tooltip', data);

		$el.append($tooltip);
		$('#connectionscontid').append($el);

		this.addConnection({from: data.from.code, to: data.to.code, position: data.position}, $el);
	};



	//
	// BUILD
	//
	SmoothRouteNetwork.prototype.build = function()
	{
		networkmap = new SmoothNetworkMap();

		this.buildAirports();

		this.buildConnections();
	};
	// build
	//



	SmoothRouteNetwork.prototype.render = function(options)
	{
		$( ".iconplane", "#connectionscontid").css('transition','none');

		this.clear();
		this.positionAirports();
		this.renderConnectionsBezier(options);
	};


	SmoothRouteNetwork.prototype.clear = function()
	{
		this.ctx.clearRect(0, 0, width, height);
	};


	SmoothRouteNetwork.prototype.resize = function( w, h )
	{
		width = w;
		height = h;

		this.c.width = w;
		this.c.height = h;
		this.cl.width = w;
		this.cl.height = h;

		if(networkmap){
			networkmap.resize( w, h );
			if(networkmap.getIsInited()){
				this.render();
			}
		}
	};


	SmoothRouteNetwork.prototype.show = function()
	{
		$("#routenetworkmaincontid").css({"display":"block"});
	};


	SmoothRouteNetwork.prototype.hide = function()
	{
		var bg = $("#routenetworkelementsbackgroundid");
		bg.css({"z-index":""});

		if( this.currentElement )
		{
			this.currentElement.hideTooltip();
			this.currentElement = null
		}
		$("#routenetworkmaincontid").css({"display":"none"});
	};


	SmoothRouteNetwork.prototype.gotoPosition = function( pos )
	{

		if ( pos === this.currentMapPosition ) {
			return;
		}

		this.currentMapPosition = pos;

		if(networkmap){

			if( Math.abs( this.currentPos-pos ) < 10 )
			{
				return;
			}

			this.currentPos = pos;

			var norm = pos/(this.zDiff*2);

			norm = MathX.range(norm, -0.5, 1);

			networkmap.setPosition( norm );

			if( norm > 1 )
			{
				var a = 5 - 4*norm;
			}
			else if( norm < 0 )
			{
				var a = 1+ norm*4;
			}
			else
			{
				var a = 1;
			}
			this.setAlpha( a );

			this.render();

			if ( norm >= -0.01 ) {
				return true; // route network visible
			}
		}
		return false;
	};


	SmoothRouteNetwork.prototype.setAlpha = function( a )
	{
		if(this.currentA != a)
		{
			this.currentA = a;

			this.cont.css({ 'opacity':Number(a).toFixed(15) });
		}
	}


	//
	// AIRPORTS
	//
	SmoothRouteNetwork.prototype.buildAirports = function()
	{
		var a = $( ".airport", "#airportscontid");
		var me = this;

		for( var i=0; i<airports.length; i++ )
		{
			var el = $( a[i] );
			var airport = new Airport( el, airports[i] );
			airportsEl.push( airport );

			$( airport ).bind( "ontooltipopen", function() { me.onTooltipOpen( this ); } );
			$( airport ).bind( "ontooltipclose", function() { me.onTooltipClose( this ); } );
		}
	};


	SmoothRouteNetwork.prototype.onTooltipOpen = function( el )
	{
		this.currentElement = el;
		this.render({ forceBezier: true });
		this.showBackground();

		this.$html.addClass('has-overlay');
	};
	SmoothRouteNetwork.prototype.onTooltipClose = function( el )
	{
		this.hideBackground();
		this.currentElement = null;
		this.render({ forceBezier: true });

		this.$html.removeClass('has-overlay');
	};

	SmoothRouteNetwork.prototype.positionAirports = function()
	{
		var ncp = networkmap.getContPos();
		var ns = networkmap.getScale();

		this.airportPosition = [];

		for( var i=0; i<airports.length; i++ )
		{
			var d = airports[i];
			var p = d.position;
			var px = (+p.x)*ns-ncp.x;
			var py = (+p.y)*ns-ncp.y;

			this.airportPosition[i] = {
				el: airportsEl[i],
				index: i,
				icon: {
					x: px,
					y: py
				}
			};

			// airportsEl[i].setPosition(px, py, width, height );
			// airportsEl[i].place();

			this.ctx.save();
			this.ctx.translate(px, py);
			this.ctx.drawImage( airportImage, - 5, - 5 );
			this.ctx.restore();


			if ( this.recentHover == airportsEl[i] ) {
				this.recentHover.setPosition(px, py);
				this.recentHover.place();
			}

		}
	};


	SmoothRouteNetwork.prototype.getAirportPosition = function( aiportCode )
	{
		for( var i=0; i<airports.length; i++ )
		{
			var d = airports[i];

			for( var j=0; j<d.code.length; j++ )
			{
				if( aiportCode == d.code[j] )
				{
					return new Point( d.position.x, d.position.y );
				}
			}
		}
		return new Point( 0, 0 );
	};
	// airports
	//


	//
	// CONNECTIONS
	//
	SmoothRouteNetwork.prototype.buildConnections = function()
	{
		var a = $( ".iconplane", "#connectionscontid");

		var me = this;

		for( var i=0; i<connections.length; i++ )
		{
			var d = connections[i];
			var el = $( a[i] );

			this.addConnection(d, el);
		}
	};

	SmoothRouteNetwork.prototype.addConnection = function(d, el)
	{
		connectionCounter++;
		var airplane = new Airplane( el, d, connectionCounter );
		planesEl.push(airplane);

		planes.push( { el:el, from:this.getAirportPosition(d.from), to:this.getAirportPosition(d.to), pos:d.position } );

		var me = this;
		$( airplane ).bind( "ontooltipopen", function() { me.onTooltipOpen( this ); } );
		$( airplane ).bind( "ontooltipclose", function() { me.onTooltipClose( this ); } );
	};

	SmoothRouteNetwork.prototype.getBezierData = function(scale)
	{
		var ns = scale;
		var ncp = networkmap.getContPos(scale);


		var i, d, el, pos, from, to, c1x, c1y, c2x, c2y, c1, c2, p, p2, deltaY, deltaX, angleInDegrees;

		var curves = [], completedHash = {};

		for( i=0; i<planes.length; i++ )
		{
			d = planes[i];
			el = d.el;
			pos = d.pos;

			from = new Point( d.from.x, d.from.y);
			from.x = +from.x*ns-ncp.x;
			from.y = +from.y*ns-ncp.y;

			to = new Point( d.to.x, d.to.y );
			to.x = +to.x*ns-ncp.x;
			to.y = +to.y*ns-ncp.y;

			c1x = (to.x-from.x)*0.2+from.x;
			c1y = Math.min( from.y, to.y )-Math.abs(to.x-from.x)*0.22;

			c2x = (to.x-from.x)*0.8+from.x;
			c2y = Math.min( from.y, to.y )-Math.abs(to.x-from.x)*0.22;

			c1 = new Point( c1x, c1y );
			c2 = new Point( c2x, c2y );

			var bezierpos = planesEl[i].getPositionBezier();
			if( bezierpos )
			{
				p = new Point();
				p.x = bezierpos.x*ns-ncp.x;
				p.y = bezierpos.y*ns-ncp.y;

				angleInDegrees = bezierpos.a;
			}
			else
			{
				p = MathX.deCasteljau( +pos, from, to, c1, c2 );
				p2 = MathX.deCasteljau( +pos+0.001, from, to, c1, c2  );

				//angle
				deltaY = p2.y - p.y;
				deltaX = p2.x - p.x;
				angleInDegrees = Math.atan(deltaY / deltaX) * 180 / Math.PI+90;

				if(p.x>p2.x)
				{
					angleInDegrees+=180;
				}


				planesEl[i].setPositionBezier( (p.x +ncp.x )/ns, (p.y +ncp.y )/ns, angleInDegrees );
			}


			//if an airplane is choosen - show gradient
			//if( this.currentElement && this.currentElement.getId && this.currentElement.getId() == i )
			var isGradient = false, rad = false, gradientPos;
			if( this.currentElement && this.currentElement.getData )
			{
				var d1 = this.currentElement.getData();
				var d2 = planesEl[i].getData();
				if( d1.from == d2.from && d1.to == d2.to )
				{
					rad = this.cltx.createLinearGradient( from.x, from.y, to.x, from.y );
					rad.addColorStop(0, '#CA1413');

					gradientPos = Math.abs( (p.x-from.x)/(to.x-from.x) );
					gradientPos = gradientPos?gradientPos:0;

					rad.addColorStop( gradientPos, '#CA1413');
					rad.addColorStop( (gradientPos+.00001)%1, '#ffffff');

					rad.addColorStop( 1, '#ffffff');

					isGradient = true;
				}
			}

			var iconScale = (1-Math.abs(0.5-pos)/1.2)*0.6;
			var iconRotation = angleInDegrees;

			curves.push({
				el: planesEl[i],
				index: i,
				start: [from.x, from.y],
				curve: [c1.x, c1.y, c2.x, c2.y, to.x, to.y],
				gradient: rad,
				icon: { x: p.x, y: p.y, scale: iconScale, rotation: iconRotation }
			});

		}

		return curves;
	};


	SmoothRouteNetwork.prototype.renderConnectionsBezier = function(options)
	{
		options = options || {
			forceBezier: false
		};

		var ns = networkmap.getScale();

		var pos, posdata = this.getBezierData(ns);

		// draw airplanes

		for( i=0; i<posdata.length; i++ )
		{
			pos = posdata[i];

			this.ctx.save();
			this.ctx.translate( pos.icon.x, pos.icon.y );
			this.ctx.scale( pos.icon.scale, pos.icon.scale );
			this.ctx.rotate( pos.icon.rotation / 180 * Math.PI );
			this.ctx.drawImage( planeImage, -12, -14 );
			this.ctx.restore();

			if ( this.recentHover == planesEl[i] ) {
				this.recentHover.setPosition(pos.icon.x, pos.icon.y);
				this.recentHover.place(pos.icon.rotation, pos.icon.scale);
			}
		}


		this.airplanePosition = posdata;


		// only redraw curves for certain scaling

		var curveScale = Math.log(ns) / Math.LN2;
		curveScale = Math.floor(curveScale * 3) / 3;
		curveScale = Math.pow(2, curveScale);

		if ( curveScale !== this.clScale || options.forceBezier ) {
			this.clScale = curveScale;

			posdata = this.getBezierData(curveScale);
			// console.log("Redrawing curves")


			this.cltx.clearRect(0, 0, width, height);

			// draw gradient lines (selected items)

			for( i=0; i<posdata.length; i++ )
			{
				pos = posdata[i];

				if( pos.gradient )
				{
					this.cltx.beginPath();
					this.cltx.lineWidth= 0.4;
					this.cltx.strokeStyle = pos.gradient;
					this.cltx.moveTo.apply(this.cltx, pos.start);
					this.cltx.bezierCurveTo.apply(this.cltx, pos.curve);
					this.cltx.stroke();
				}
			}

			// draw normal lines

			this.cltx.save();
			this.cltx.beginPath();
			this.cltx.lineWidth= 0.4;
			this.cltx.strokeStyle = 'rgba(0,0,0,.15)';

			for( i=0; i<posdata.length; i++ )
			{
				pos = posdata[i];

				if( !pos.gradient )
				{
					this.cltx.moveTo.apply(this.cltx, pos.start);
					this.cltx.bezierCurveTo.apply(this.cltx, pos.curve);
				}
			}

			this.cltx.stroke();
			this.cltx.restore();

		}

		Helpers.translate(this.cl, 0, 0, 0, 0, ns/this.clScale);
	};



	SmoothRouteNetwork.prototype.checkMouseMove = function( x, y ) {
		var pos = this.findElementAt(x, y);

		this.setHover(pos);
	};


	SmoothRouteNetwork.prototype.setHover = function( pos ) {
		if ( pos && pos.el == this.recentHover ) {
			return pos;
		}

		if ( this.recentHover && this.recentHover.tooltipOpened ) {
			return pos;
		}

		if ( this.recentHover ) {
			this.recentHover.hide();
		}

		this.recentHover = pos && pos.el;

		if ( pos ) {
			this.recentHover.setPosition( pos.icon.x, pos.icon.y );
			this.recentHover.place(pos.icon.rotation, pos.icon.scale);
			this.recentHover.show(true); // true: show tooltip label
		}


		this.cont.css('cursor', pos ? 'pointer' : '');

		return pos;
	};



	SmoothRouteNetwork.prototype.checkClick = function( x, y ) {

		var pos = this.checkMouseMove(x, y);
		if ( this.recentHover ) {
			this.recentHover.showTooltip();
		}
	};



	SmoothRouteNetwork.prototype.findElementAt = function( x, y ) {

		var minIndex = -1, minDist = 20 * 20, pos, dist, dx, dy;

		var positions = this.airplanePosition.concat(this.airportPosition);

		for( i=0; i<positions.length; i++ )
		{
			pos = positions[i].icon;

			dx = pos.x - x;
			dy = pos.y - y;

			if ( Math.abs(dx) < 20 && Math.abs(dy) < 20 ) {
				dist = dx * dx + dy * dy;
				if ( dist < minDist ) {
					minDist = dist;
					minIndex = i;
				}
			}
		}

		return minIndex >= 0 ? positions[minIndex] : null;
	};




	SmoothRouteNetwork.prototype.openConnection = function( connectionId )
	{
		if( this.currentElement )
		{
			this.currentElement.hideTooltip();
			this.currentElement.hide();
			this.currentElement = null
		}

		for( var i=0; i<connections.length; i++ )
		{
			if(connections[i].code == connectionId )
			{
				this.setHover( this.airplanePosition[i] );
				planesEl[i].showTooltip();
			}
		}
	};

	// connections
	//

	//
	// GREY BACKGROUND
	//
	SmoothRouteNetwork.prototype.showBackground = function()
	{
		var bg = $("#routenetworkelementsbackgroundid");
		bg.css({display: 'block', opacity: 0}).animate({
			opacity: 1,
			width: '101%'
		}, 300);
	};
	//drogi komputerze prosze o zastosowanie w tym miejscu odpowiedniej formu
	//dziekuje uprzejmie zycze milego dnia i prosze pozdrowic zone

	SmoothRouteNetwork.prototype.hideBackground = function()
	{
		var bg = $("#routenetworkelementsbackgroundid");
		bg.css({ zIndex: '', width: '100%' }).stop().fadeOut();
	};

	SmoothRouteNetwork.prototype.onBgClick = function()
	{
		if( this.currentElement ) this.currentElement.hideTooltip();
	};
	// grey background
	//


	return SmoothRouteNetwork;

});

define(
	'app/routenetwork/RouteNetworkController.class',['jquery', 'app/routenetwork/SmoothRouteNetwork.class', 'app/Config' ],
	function( $, SmoothRouteNetwork, Config ){


	var routeNetwork;

	var isStopped = false;


	function RouteNetworkController( routenetworkZPos )
	{
		this.zPos = routenetworkZPos;

		if( Config.get("isRouteNetworkOff") == "true" )
		{
			this.isRouteOff = true;
		}
		else
		{
			this.isRouteOff = false;
			this.buildRouteNetwork();
		}

		//this.stop();
	}


	RouteNetworkController.prototype.resize = function( windowW, windowH )
	{
		if( !this.isRouteOff ) routeNetwork.resize( windowW, windowH );
	};


	RouteNetworkController.prototype.buildRouteNetwork = function()
	{
		c = $('#routenetworkcanvasid')[0];
		ctx = c.getContext("2d");

		routeNetwork = new SmoothRouteNetwork( c, ctx );
	};
	
	RouteNetworkController.prototype.openConnection = function( connectionId )
	{
		if( !this.isRouteOff ) routeNetwork.openConnection( connectionId );
	};




	RouteNetworkController.prototype.updateCameraPosition = function( pos )
	{
		if( isStopped || this.isRouteOff ) return;
		
		return routeNetwork.gotoPosition(pos.z - this.zPos);
	};


	RouteNetworkController.prototype.stop = function()
	{
		if( isStopped || this.isRouteOff ) return;

		isStopped = true;
		routeNetwork.hide();

		clearInterval(this.updateInterval);
		this.updateInterval = false;
	};

	RouteNetworkController.prototype.play = function()
	{
		var me = this;
		if( !isStopped || this.isRouteOff ) return;

		isStopped = false;
		routeNetwork.show();

		if ( !this.updateInterval ) {
			setTimeout(function(){
				routeNetwork.update();
			},5000);
			this.updateInterval = setInterval(function(){
				routeNetwork.update();
			},30000);
		}
	};

	return RouteNetworkController;
});

define('app/controllers/Dictionary',['jquery'], function($){
	
	var data = {
		next:"Weiter auf Route - %themeRouteName%",
		prev:"Zurück auf Route - %themeRouteName%"
	};

	var data = $.extend({}, data, window.app_dictionary);

	return {
		get: function(key) { return data[key]; },
		set: function(d) { data = d; }
	};
});

define(
	'app/content/Navigation',[
		'jquery', 'app/plugins/mediaDispatcher'
	],
	function(
		$,mediaDispatcher
	) {
		var ns = '.navigation';
		var $el,
			$trigger,
			$bookingButton,
			$world3d,
			$window;

		function Navigation() {
			this.$el = $('.js-navigation');
			this.$trigger = $('.js-navigation-toggle');
			this.$closeBtn = $(".js-close-btn");
			this.$world3dContainer = $('#js-world3d-container');
			this.$mainnav = $('#js-main-nav');
			this.$subnav = $($('.js-navigation-subnav').attr("href"));
			this.$navLinks = $(".js-main-nav__link");
			this.$footer = $(".js-main-nav__footer");
			this.$footerList = $(".js-main-nav__footer__list");
			this.hoverTimer = null;
			this.velocity = 70;
			this.isClosedOnce = false;
			this.hasHashValue = false;
			this.firstTime = true;
			this.$window = $(window);

			self = this;

			this.initListeners();
			this.positionFooter();
			if(window.location.hash && (window.location.hash).length > 0){
				this.hasHashValue = true;
			}
		}

		Navigation.prototype.initListeners = function() {
			var self = this;

			this.$trigger.on('click' + ns + ' touchstart' + ns, function(e) {
				e.preventDefault();
				e.stopPropagation(); // to keep closing right away
				var isActive = self.$el.hasClass('is-active');
				self.$el.trigger('wos-navigation-toggle-click', [isActive]);
				self.toggleNavigation(isActive);

			});

			this.$el.on('mousemove' + ns + ' scroll' + ns + ' mousewheel' + ns + ' touchmove' + ns + ' touchstart' + ns + ' touchend' + ns, function(e) {
				e.stopPropagation();
			});

			this.$el.on("mouseover"+ns, function(e){
				self.$el.addClass("is-hovered");
			});

			this.$el.on("mouseleave"+ns, function(e){
				self.$el.removeClass("is-hovered");	
			});

			this.$closeBtn.on('click'+ns, function(e){
				e.preventDefault();
				self.toggleNavigation(true);
			});

			this.$el.on('click' + ns, '.js-main-nav__link', function(e) {
				var href = $(this).attr('href');
				var $goToContentLink = false;

				$(this).trigger("wos-navigation-link-click", [href]);

				// a little delay feels a little better
				setTimeout(function(){
					self.closeNavigation();
				}, 100);
			});

			this.$navLinks.on('mouseover'+ns, function(e){
				clearTimeout(self.hoverTimer);
				self.$mainnav.addClass("is-hovered");
				self.$navLinks.removeClass('is-active');
				var $target = $(e.target).closest('.js-main-nav__link');
				$target.addClass("is-active");
			});

			this.$navLinks.on('mouseleave'+ns, function(e){
				self.hoverTimer = setTimeout(function(){
					self.$mainnav.removeClass("is-hovered");
					self.$navLinks.removeClass('is-active');	
				}, 100);
			});

			$(document).on('world3d:intro:show'+ns, function(e){
				self.openHandler();
			});

			$(document).on('world3d:intro:hide'+ns, function(e){
				self.closeHandler();
			});

			$('.js-navigation-subnav').on('click' + ns, this.handleSubnavigation);

			this.$window.on('resize'+ns, function(e){
				self.positionFooter();
			});

			mediaDispatcher.isOrBelow('mobile').then(function(){
				$(document).off('world3d:intro:show'+ns);
				$(document).off('world3d:intro:hide'+ns);
				setTimeout(function(){
					self.toggleNavigation(true);
				}, 100);
		  }).otherwise(function(){
		  	setTimeout(function(){
					if(!self.hasHashValue){
						self.toggleNavigation(false);
					}else{
						if(!self.firstTime){
							self.toggleNavigation(true);
						}else{
							self.firstTime = false;
						}
					}
				}, 100);
		  	
		  });

		  this.$window.on('orientationchange'+ns, function(){
		  	var isVisible = self.$el.hasClass('is-active');
		  	self.toggleNavigation(!isVisible);
		  });
		  
		};

		Navigation.prototype.closeHandler = function(){
			if(this.$el.hasClass('is-active') && !this.$el.hasClass('is-hovered')){
				self.toggleNavigation(true);
			}
		}

		Navigation.prototype.openHandler = function(){
			if(!this.$el.hasClass('is-active')){
				self.toggleNavigation(false);
			}
		}


		Navigation.prototype.positionFooter = function(){
			var height = this.$footerList.outerHeight();

			if(this.$footer.offset().top+height < this.$window.height()){
				height = this.$window.height()-this.$footer.offset().top
			}

			this.$footer.css({
				'height':height+"px"
			});
		}

		Navigation.prototype.toggleNavigation = function(isVisible) {
			var pos;
			if (isVisible) {
				//close navigation
				if(!this.isClosedOnce){
					this.isClosedOnce = true;
					this.$el.off("mouseover"+ns);
					this.$el.off("mouseleave"+ns);
					this.$el.removeClass("is-hovered");
				}
				this.$el.removeClass('is-active');
				$('body').removeClass('is-navigation-visible').off('click' + ns + ' touchstart' + ns, self.closeNavigation);
				this.$el.trigger('closed' + ns);
			}else{
				//open navigation
				this.$el.addClass('is-active');
				$('body').addClass('is-navigation-visible').on('click' + ns + ' touchstart' + ns, self.closeNavigation);
				this.$el.trigger('opened' + ns);
			}
			
			if (Modernizr.csstransitions && Modernizr.csstransforms) {
				pos = !isVisible ? 0 : (this.$el.outerWidth()) + 'px';
				this.$el.css({
					'transform': 'translateX(' + pos + ') translateZ(10200px)',
					'transition': 'all 400ms ease-out'
				});
			} else {
				pos = !isVisible ? 0 : (this.$el.outerWidth()*-1) + 'px',

				this.$el.stop().animate({
					'right': pos,
				}, 400);
			}

		};

		Navigation.prototype.closeNavigationByMousewheel = function(delta){
			this.toggleNavigation(true);
		}

		Navigation.prototype.closeNavigation = function(e) {
			if(e == undefined || !$(e.target).parents(".dotsnavigationinner, #main-nav").length){
				self.toggleNavigation(true);
			}
		};

		Navigation.prototype.handleSubnavigation = function(e) {
			e.preventDefault();

			var $this = $(this),
				$mainnav = $('#js-main-nav');
				$subnav = $($this.attr('href')),
				mainnavWidth = $mainnav.outerWidth();

			//var timeout;

			function showNavigation(isvisible) {
				var mainLeft = isvisible ? '-100%' : '0';
				var subLeft = isvisible ? '0' : '100%';
				if (Modernizr.csstransitions && Modernizr.csstransforms) {
					$mainnav.css({
						'transform': 'translateX(' + mainLeft + ') translateZ(10200px)',
						'transition': 'all 400ms',
					});

					$subnav.css({
						'transform': 'translateX(' + subLeft + ') translateZ(0)',
						'transition': 'all 400ms'
					});
				} else {
					$mainnav.animate({
						'transform': 'translateX(0)',
						'transition': 'none',
						'left': mainLeft,
						'overflow-y': isvisible ? 'hidden' : 'scroll'
					}, 400);

					$subnav.css({
						'left': subLeft,
						'transform': 'translateX(0)',
						'transition': 'none'
					});
				}
			}

			showNavigation(true);

			$('.js-subnav-back').one('click' + ns, function(e) {
				e.preventDefault();
				showNavigation(false);
			});
		};


		Navigation.prototype.destroy = function() {
			$(document).off(ns);
			$(window).off(ns);
			self = null;
		};

		Navigation.prototype.inTarget = function(eleArr,eventTarget){
			for (var i = 0; i < eleArr.length; i++) {
				if($.contains( eleArr[i], eventTarget ) || eleArr[i] == eventTarget){
					return true;
				}
			}
			return false;			
		}

		return Navigation;
	});

define(
	'app/modules/RoundMask.class',['jquery', 'hv/util/MathX'],
	function($, MathX) {

	function RoundMask() {
		this.circle = document.getElementById('contentcontainerid');
		this.inner = document.getElementById('contentinnercontid');
		this.$circle = $(this.circle);

		this.x;
		this.y;

		this.isRetina = this.checkRetina();
	}

	RoundMask.prototype.show = function(xpos, ypos, callback) {
		var self = this;

		this.ww = $(window).width();
		this.wh = $(window).height();

		this.x = xpos || this.ww * 0.5;
		this.y = ypos || this.wh * 0.5;

		var $circle = this.$circle

		var maskRadius =  Math.max(
				Math.sqrt(Math.pow(self.x, 2) + Math.pow(self.y, 2)), //dist. top left corner
				Math.sqrt(Math.pow(self.x, 2) + Math.pow(self.wh - self.y, 2)), //dist. bottom left corner

				Math.sqrt(Math.pow(self.ww - self.x, 2) + Math.pow(self.y, 2)), //dist. top right corner
				Math.sqrt(Math.pow(self.ww - self.x, 2) + Math.pow(self.wh - self.y, 2)) //dist. bottom right corner
			);

		if(Modernizr.cssmask) {
			$circle.trigger('showTransitionStart.roundMask');

			$circle.css({
				'-webkit-mask-size' : '10px',
				'transition' : '',
				'position' : 'absolute',
				'top' : 0,
				'left' : 0,
				'right' : 0,
				'bottom' : 0,
				'overflow' : 'hidden',
				'display' : 'block',
				'transition' : 'none'
			});

			$circle.css({
				'transition' : '-webkit-mask-size 500ms linear',
				'-webkit-mask-size' : ((maskRadius * 2) + 200) +'px',
				'-webkit-mask-position' : Math.min((this.x / this.ww * 100), 100) + '% ' + Math.min((this.y / this.wh * 100), 100) +'%',
			}).on('webkitTransitionEnd transitionend transitionEnd msTransitionEnd oTransitionEnd', onMaskTransitionEnd);

			function onMaskTransitionEnd(e) {
				e.stopPropagation();

				var propertyName = e.originalEvent.propertyName;
				
				if(propertyName === '-webkit-mask-size') {
					self.$circle.off('webkitTransitionEnd transitionend transitionEnd msTransitionEnd oTransitionEnd', onMaskTransitionEnd);

					self.$circle.css({
						'-webkit-mask-image': 'none'
					});

					if (callback) {
						callback();
					}

					self.$circle.trigger('showTransitionEnd.roundMask');
				}
			}
		} else {
			/*var maxr = Math.sqrt(this.ww * this.ww + this.wh * this.wh);
			maxr = Math.min(2000, maxr);*/
			maxr = maskRadius + 50;

			this.tmp = 30;

			var me = this;

			me.render(me.x, me.y, 0);

			$(this).animate({
				tmp: maxr / 2
			}, {
				duration: 500,
				start: function() {
					this.$circle.trigger('showTransitionStart.roundMask');
				},
				step: function(now, fx) {
					me.render(me.x, me.y, now);
				},
				complete: function() {
					// let's make sure our container is resizable
					this.circle.style.left = '0px';
					this.circle.style.top = '0px';
					this.circle.style.width = '100%';
					this.circle.style.height = '100%';
					this.inner.style.left = '0px';
					this.inner.style.top = '0px';
					this.inner.style.width = '100%';
					this.inner.style.height = '100%';
					this.circle.style.borderRadius = '0px';
					this.circle.style.webkitMask = 'none';

					this.$circle.trigger('showTransitionEnd.roundMask');

					if (callback) {
						callback();
					}
				}
			});
		}
	};

	RoundMask.prototype.hide = function(callback) {
		$("#js-world3d-container").css({
			'visibility': 'visible',
			'pointer-events': '',
			'display': ''
		});

		this.ww = $(window).width();
		this.wh = $(window).height();

		this.x = this.x || this.ww * 0.5;
		this.y = this.y || this.wh * 0.5;

		if(Modernizr.cssmask) {
			this.$circle.trigger('hideTransitionStart.roundMask');

			var self = this;

			this.$circle.css({
				'-webkit-mask-image' : '',
				'-webkit-mask-size' : '10px',
				'transition' : '-webkit-mask-size 500ms linear'
			}).on('webkitTransitionEnd transitionend transitionEnd msTransitionEnd oTransitionEnd', onMaskTransitionHideEnd);

			function onMaskTransitionHideEnd(e) {
				e.stopPropagation();

				var propertyName = e.originalEvent.propertyName;
				
				if(propertyName === '-webkit-mask-size') {
					self.$circle.off('webkitTransitionEnd transitionend transitionEnd msTransitionEnd oTransitionEnd', onMaskTransitionHideEnd);

					if (callback) {
						callback();
					}

					self.$circle.trigger('hideTransitionEnd.roundMask');
				}
			}
		} else {
			var maxr = Math.sqrt(this.ww * this.ww + this.wh * this.wh);
			maxr = Math.min(2000, maxr);

			this.tmp = maxr / 2;

			var me = this;

			// me.render(me.x, me.y, this.tmp);

			$(this).animate({
				tmp: 0
			}, {
				duration: 500,
				start: function() {
					this.$circle.trigger('hideTransitionStart.roundMask');
				},
				step: function(now, fx) {
					me.render(me.x, me.y, now);
				},
				complete: function() {
					if (callback) {
						callback();
					}
					this.$circle.trigger('hideTransitionEnd.roundMask');
				},
			});
		}
	};

	RoundMask.prototype.checkRetina = function() {
		var mediaQuery = "(-webkit-min-device-pixel-ratio: 1.5), (min--moz-device-pixel-ratio: 1.5), (-o-min-device-pixel-ratio: 3/2), (min-resolution: 1.5dppx)";
		if (window.devicePixelRatio > 1)
			return true;
		if (window.matchMedia && window.matchMedia(mediaQuery).matches)
			return true;
		return false;
	};

	RoundMask.prototype.render = function(x, y, r) {
		this.circle.style.position = 'absolute';
		this.circle.style.left = (x - r) + 'px';
		this.circle.style.top = (y - r) + 'px';
		this.circle.style.width = (r + r) + 'px';
		this.circle.style.height = (r + r) + 'px';
		this.circle.style.borderRadius = '100%';
		this.circle.style.overflow = 'hidden';
		this.inner.style.position = 'absolute';
		this.inner.style.left = (r - x) + 'px';
		this.inner.style.top = (r - y) + 'px';
		this.inner.style.width = this.circle.parentElement.clientWidth + 'px';
		this.inner.style.height = this.circle.parentElement.clientHeight + 'px';

		this.circle.style.webkitMask = '';
		this.circle.style.webkitMaskSize = (r + r) + 'px';
	};

	return RoundMask;
});

define (
	'app/modules/Intro.class',['jquery',  'app/plugins/mediaDispatcher' ],
	function( $, mediaDispatcher){


 
	function Intro()
	{
		this.$outercontainer = $("#introcontentid");
		this.$container = $(".introinner"); 
		this.$enter = $(".introcalltoaction"); 
		this.$loader= $(".introloader"); 
		this.$background = $(".introbackground");
		this.topValue = (this.$container.position().top);
		this.init();
	}


	Intro.prototype.init = function()
	{
		var self = this;
		//this.$container.css( { "opacity":"0" } );
		this.$enter.css({"opacity":"0"});

		mediaDispatcher.isOrBelow('mobile').then(function(){
			self.$container.stop().removeAttr("style");
	  });
	}

	Intro.prototype.show = function()
	{
		this.$container.stop().animate( { "opacity":"1", "top":this.topValue+"px" }, 600 );
		this.$outercontainer.css( { "display":"block" } );
		this.$outercontainer.stop().animate( { "opacity":"1" }, 400);
	};

	Intro.prototype.loaded = function()
	{
		if(Modernizr.csstransitions) {
			this.$loader.css({
				'opacity' : 0,
				'visibility' : 'hidden',
				'transition' : 'visibility 100ms, opacity 100ms' 
			});

			this.$enter.css({
				'opacity' : 1,
				'transition' : 'opacity 700ms' 
			});

			this.$background.css({
				'opacity' : 0,
				'visibility' : 'visible',
				'transition' : 'visibility 100ms, opacity 100ms' 
			});


		} else {
			this.$loader.animate( { "opacity":"0" }, 700 );
			this.$enter.animate( { "opacity":"1" }, 700 );

			this.$background.animate( { "opacity":"0" }, 700 );
		}
	};

	Intro.prototype.hide = function()
	{
		this.$container.stop().animate( { "opacity":"0", "top":(this.topValue-35)+"px" }, 600 );
		var me = this;
		this.$outercontainer.stop().animate( { "opacity":"0" }, 400, function() {
    		// me.$outercontainer.remove();//.css( { "display":"none" } );
    		me.$outercontainer.css( { "display":"none" } );
		});
	};



	return Intro;
});

define('app/util/Utils',[], function(){

	var Utils = function() {
		if (typeof Utils.prototype.instance === 'object') {
			return Utils.prototype.instance;
		}
		Utils.prototype.instance = this;
	};

	/**
	* Creates a function that will delay the execution of "func" until after "wait" milliseconds have elapsed since the last time it was invoked
	**/
	Utils.prototype.debounce = function(func, wait, immediate) {
		var timeout;

		return function() {
			var obj = this,
				args = arguments;

			if(timeout) {
				clearTimeout(timeout);
			}

			timeout = setTimeout(function() {
				func.apply(obj, args);
				timeout = null;
			}, wait || 100);
			if(immediate) {
				func.apply(obj, args);
			}
		};
	};

	/**
	 * Checks if the specified value is undefined
	 *
	 * @param  {[type]}  value [description]
	 * @return {Boolean}       [description]
	 */
	Utils.prototype.isUndefined = function(value) {
		return (typeof value === 'undefined');
	};

	/**
	 * Checks if the specified value is defined
	 *
	 * @param  {[type]}  value [description]
	 * @return {Boolean}       [description]
	 */
	Utils.prototype.isDefined = function(value) {
		return !this.isUndefined(value);
	};

	/**
	 * Checks if the specified value isn't null and isn't undefined.
	 *
	 * @param  {[type]}  value [description]
	 * @return {Boolean}       [description]
	 */
	Utils.prototype.isAssigned = function(value) {
		return (!this.isUndefined(value) && value !== null);
	};

	/**
	 * Returns the value if it is assigned, otherwise returns the defaultValue
	 * @param  value        Value
	 * @param  defaultValue Default Value
	 * @return              defined variable
	 */
	Utils.prototype.defaultValue = function(value, defaultValue) {
		return this.isAssigned(value) ? value : defaultValue;
	};

	/**
	* Removes leading and trailing whitespaces from a string.
 	**/
	Utils.prototype.trim = function(str) {
		if (str.trim) {
   			return str.trim();
		}

		return str.replace(/^\s+|\s+$/g, '');
	};

	/*
	* Pads numbers with leading zeros. Not the savest impl. though. ;-)
	*/
	Utils.prototype.pad = function(num, size) {
		var s = "000000" + num;
		return s.substr(s.length-size);
	};

	/**
	 * Rounds the given number on n-decimals.
	 *
	 * @param  num      number
	 * @param  decimals number of decimals
	 * @return          rounded number
	 */
	Utils.prototype.round = function(num, decimals) {
		return Number(Math.round(num + 'e' + decimals) + 'e-' + decimals);
	};


	/**
	 * easeInCubic
	 *
	 * @param  t current time (frames or miliseconds)
	 * @param  b start value
	 * @param  c change in value
	 * @param  d duration (frames or miliseconds)
	 * @return   [description]
	 */
	Utils.prototype.easeInCubic = function (t, b, c, d) {
		t /= d;
		return c*t*t*t + b;
	};

	/**
	 * Takes a function and returns a new one that will always have a particular context.
	 *
	 * @param  {[type]} fnc [description]
	 * @return {[type]}     [description]
	 */
	Utils.prototype.bind = function(fnc) {
		var self = this;
		return function(){
			method.apply(self, arguments);
		};
	};

	Utils.prototype.getParameterByName = function(name, href) {
		if (!href) href = location.href;
	    var regex = new RegExp("\\W" + name + "=([^#\\?\\&]*)"),
	        results = regex.exec(href);
	    return results === null ? false : decodeURIComponent(results[1].replace(/\+/g, " "));
	};


	return (new Utils());
});

define (
'app/content/Hotspot',[
	'jquery'
],
function(
	$
) {
	var ns = '.hotspot';
	var self,
		$el;

	var parentHeight,
		parentWidth,
		trigger;

	function Hotspot($element, parentHeight, parentWidth, trigger) {
		self = this;
		self.$el = $element;

		self.trigger = trigger || 'click';

		self.parentHeight = parentHeight;
		self.parentWidth = parentWidth;

		if(parentHeight && parentWidth) {
			self.positionHotspot();
		}

		self.positionTooltip();

		self.registerListeners();

		return this;
	}

	/**
	 * Converts px values to percentage and sets it.
	 */
	Hotspot.prototype.positionHotspot = function() {
		var position = self.$el.data('position'),
			halfHotspotWidth = this.$el.outerWidth() / 2;

		if(position) {
			self.$el.css({
				'top' : Math.round((100 / self.parentHeight * position[1])) + '%',
				'left' : Math.round((100 / self.parentWidth * position[0])) + '%',
				'margin-left' : Math.round(halfHotspotWidth) * -1,
				'margin-top' : Math.round(halfHotspotWidth) * -1
			});
		}
	};

	Hotspot.prototype.registerListeners = function() {
		self.$el.on(self.trigger + ns, self.onClickHandler);
	};

	Hotspot.prototype.onClickHandler = function(e) {
		e.preventDefault();

		var $hotspot = $(e.target),
			$parent = $hotspot.closest('.js-slideshow-slide'),
			$overlay;

		if($parent.find('.js-overlay').length === 0) {
			$overlay = $('<div class="js-overlay slideshow__overlay"></div>');
			$overlay.prependTo($parent);
		} else {
			$overlay = $parent.find('.js-overlay');
		}

		if(!$hotspot.hasClass('is-open')) {
			// setTimeout for css transition
			setTimeout(function() {
				$overlay.addClass('is-visible');
			},0);

			self.$el.trigger('open'+ns);
			// self.$el.trigger('wos-slideshow-hotspot-open');

			$(document).one('closeInfobox.slideshow', function(e) {
				$overlay.removeClass('is-visible');
				
				self.$el.trigger('close'+ns);
				// self.$el.trigger('wos-slideshow-hotspot-close');
			});
		}

		// self.$el.trigger('wos-slideshow-hotspot-click');
	};

	Hotspot.prototype.positionTooltip = function() {
		var $tooltip = self.$el.find('.js-tooltip'),
			$tooltipArrow = $tooltip.find('.hotspot-tooltip__arrow'),
			hotspotInnerWidth = self.$el.innerWidth(),
			offsetLeft = (hotspotInnerWidth / 2);

		if(self.$el.offset().top > 100) { //position it on top
			$tooltip.css({
				'top': '-80px',
				'left': ($tooltip.outerWidth() / -2) + offsetLeft
			});
			$tooltipArrow.removeClass('hotspot-tooltip__arrow--top').addClass('hotspot-tooltip__arrow--bottom');
		} else {
			$tooltip.css({
				'top': '40px',
				'left': ($tooltip.outerWidth() / -2) + offsetLeft
			});
			$tooltipArrow.removeClass('hotspot-tooltip__arrow--bottom').addClass('hotspot-tooltip__arrow--top');
		}

		$tooltipArrow.css({
			'left': ($tooltip.outerWidth() / 2) - ($tooltipArrow.outerWidth() / 2)
		});
	};

	Hotspot.prototype.destroy = function() {
		self.$el.off(ns);
	};

	return Hotspot;
});

define (
'app/content/FilmHotspot',[
	'jquery', 'app/content/BaseModule'
],
function(
	$, BaseModule
) {
	var ns = '.filmHotspot';
	var instanceCounter = 0;

	function FilmHotspot($element, trigger) {
		var self = this;

		self.ns = ns + (instanceCounter++);

		self.$el = $element;

		self.trigger = trigger || 'click';
		self.positionTooltip();
		self.registerListeners();

		return this;
	}

	FilmHotspot.prototype = new BaseModule();

	FilmHotspot.prototype.registerListeners = function() {
		var self = this;

		this.$el.on(this.trigger +self.ns, this.bind(this.onClickHandler));
	};

	FilmHotspot.prototype.onClickHandler = function(e) {
		var self = this;

		e.preventDefault();

		var $hotspot = $(e.target).closest('.js-hotspot'),
			$parent = $hotspot.parent('.js-video-wrapper'),
			$infobox = $($hotspot.attr('href'));

		if($parent.length === 0) {
			$parent = $hotspot.parent('.js-scroll-video');
		}

		this.$parent = $parent;

		if($hotspot.hasClass('is-hidden')) {
			return false;
		}

		if(!$hotspot.hasClass('is-open')) {
			if($parent.find('.js-overlay').length === 0) {
				self.$overlay = $('<div class="js-overlay slideshow__overlay"></div>');
				self.$overlay.insertBefore($hotspot);
			} else {
				this.$overlay = $parent.find('.js-overlay');
			}
			self.$el.trigger('infoboxOpened');
			self.$el.trigger('wos-film-hotspot-open');

			self.openInfobox($hotspot);

			// setTimeout for css transition
			setTimeout(function() {
				self.$overlay.addClass('is-visible');
			});


			$(document).one('infoboxClosed', function(e) {
				self.$overlay.removeClass('is-visible');

				self.$el.trigger('close');

				// do a timeout because of the css transition
				/*setTimeout(function() {
					self.$overlay.remove();
				}, 200);*/
			});
		} else {
			self.closeInfobox($infobox, $hotspot);
		}

		self.$el.trigger('wos-film-hotspot-click');
	};

	FilmHotspot.prototype.positionTooltip = function() {
		var self = this;

		var self = this,
			$tooltip = self.$el.find('.js-tooltip'),
			$tooltipArrow = $tooltip.find('.hotspot-tooltip__arrow'),
			hotspotInnerWidth = self.$el.innerWidth(),
			offsetLeft = (hotspotInnerWidth / 2),
			tooltipWidth = $tooltip.outerWidth();

		//if(self.$el.position().top > 100) { //position it on top
			if(tooltipWidth > 0) {
				$tooltip.css({ //ios8 bug??
					'top': '-80px',
					'left': (tooltipWidth / -2) + offsetLeft
				});
			} else {
				$tooltip.css({
					'top': '-80px',
					'width': '100px',
					'max-width': '100px',
					'white-space': 'nowrap',
					'text-ellipsis': 'overflow',
					'overflow': 'hidden',
					'text-align': 'center',
					'left': -50 + offsetLeft
				});
			}


			$tooltipArrow.removeClass('hotspot-tooltip__arrow--top').addClass('hotspot-tooltip__arrow--bottom');
		/*} else {
			$tooltip.css({
				'top': '40px',
				'left': ($tooltip.outerWidth() / -2) + offsetLeft
			});
			$tooltipArrow.removeClass('hotspot-tooltip__arrow--bottom').addClass('hotspot-tooltip__arrow--top');
		}*/

		if(tooltipWidth > 0) {
			$tooltipArrow.css({
				'left': ($tooltip.outerWidth() / 2) - ($tooltipArrow.outerWidth() / 2)
			});
		} else {
			$tooltipArrow.css({
				'left': 50 - ($tooltipArrow.outerWidth() / 2),
				'position': 'static'
			});
		}
	};

	FilmHotspot.prototype.openInfobox = function($hotspot) {
		var self = this;

		var $infobox = $($hotspot.attr('href'));
		$('html').addClass('has-infobox-open');

		self.positionInfobox($infobox, $hotspot);

		$infobox.addClass('is-visible');
		$hotspot.addClass('is-open');

		self.$overlay.on('click'+self.ns, function() {
			self.closeInfobox($infobox, $hotspot);
		});

		$('.js-infobox-close').on('click'+self.ns, function(e) {
			e.preventDefault();
			self.closeInfobox($infobox, $hotspot);
		});

		$infobox.on('click'+self.ns, function(e) {
			//e.stopPropagation();
		});

		$(window).one('keydown'+self.ns, function(e) {
			if(e.keyCode === 27) {
				self.closeInfobox($infobox, $hotspot);
			}
		});

		$(window).one('resize'+self.ns, function(e) {
			self.closeInfobox($infobox, $hotspot);
		});

		$(window).one('infoboxOpened'+self.ns, function(e) {
			self.closeInfobox($infobox, $hotspot);
		});

		var $infoboxVideo = $infobox.find('.js-infobox__video');

		if($infoboxVideo.length > 0) {
			var infoboxVideo = $infoboxVideo[0];

			if($(window).width() > 750) { //don't autoplay on mobile
				setTimeout(function() {
					infoboxVideo.load();
					
					var $playButton = $infoboxVideo.parent().find('.js-infobox__video__play');

					if($playButton.length > 0) {
						console.log('addPlayButtonClick');
						$playButton.one('click'+ns, function(e) {
							e.preventDefault();
							e.stopPropagation();
							$playButton.addClass('is-hidden');
							infoboxVideo.play();
						});
					} else {
						infoboxVideo.play();
					}

					$infoboxVideo.removeAttr('controls');

					if(self.isIOS) {
						$infoboxVideo.on('timeupdate'+ns, function(e) {
							$infoboxVideo.removeAttr('controls');
							$infoboxVideo.off('timeupdate');
						});
					}
				}, 200); //opening transition
			} else {
				$infobox.on('click'+ns, '.js-infobox__video__poster', function(){
					infoboxVideo.play();
				});
			}
		}
	};

	FilmHotspot.prototype.resetYoutubeVideo = function(iFrameEle){
		var url = iFrameEle.attr('src');
		iFrameEle.attr('src', '');
		iFrameEle.attr('src', url);
	};

	FilmHotspot.prototype.positionInfobox = function($infobox, $hotspot) {
		var self = this;

		var margin = 30,
			$infoboxArrow = $infobox.find('.infobox__arrow'),
			windowHeight = $(window).height(),
			windowWidth = $(window).width(),
			infoboxHeight = $infobox.outerHeight(),
			infoboxWidth = $infobox.outerWidth();

		var hotspotPos = {
			'x' : $hotspot.offset().left + ($hotspot.outerWidth() / 2),
			'y' : $hotspot.position().top + ($hotspot.outerHeight() / 2)
		};

		var xPos = hotspotPos.x + margin,
			yPos = hotspotPos.y - ($infobox.outerHeight() / 2);

		// position infobox vertically
		if(infoboxHeight + (margin * 2) >= windowHeight) {
			var marginTop = (windowHeight - infoboxHeight) / 2;
			yPos = marginTop;
		} else if(yPos < margin) {
			// move it a bit down
			yPos = margin;
		} else if((yPos + infoboxHeight) + margin > windowHeight) {
			yPos = windowHeight - infoboxHeight - margin;
		}

		// and the same horizontally
		if((xPos - infoboxWidth - margin) >=  margin) {
			// position infobox on the left of hotspot
			xPos = $hotspot.position().left - infoboxWidth - margin;
			$infoboxArrow.addClass('infobox__arrow--right').removeClass('infobox__arrow--left');
			$infobox.removeClass('infobox--right').addClass('infobox--left');
		} else {
			xPos = $hotspot.position().left + $hotspot.outerWidth() + margin;
			$infoboxArrow.addClass('infobox__arrow--left').removeClass('infobox__arrow--right');
			$infobox.removeClass('infobox--left').addClass('infobox--right');
		}

		xPos = Math.round(xPos);
		yPos = Math.round(yPos);
		var topVal = yPos - this.$parent.position().top;

		if($infobox.hasClass("is-centered")){
			topVal = (windowHeight-infoboxHeight)/2+(-1*this.$parent.position().top);
			xPos = (windowWidth-infoboxWidth)/2+(-1*this.$parent.position().left);
		}

		$infobox.css({
			'top': topVal,
			'left' : xPos,
			'max-height' : windowHeight
		});

		var infoboxArrowTop = ($hotspot.position().top - yPos) + ($hotspot.outerHeight() / 2);
		if($infobox.parents(".js-scroll-video-container").length){
			infoboxArrowTop = ($hotspot.position().top - yPos) + ($infoboxArrow.outerHeight() / 2);
		}

		$infoboxArrow.css({
			'top' : infoboxArrowTop
		});
		$infobox.css({
			'transform-origin': ($infobox.hasClass('infobox--left') ? 'right ' : 'left ') + (infoboxArrowTop + $infoboxArrow.outerHeight() / 2) / $infobox.outerHeight() * 100 +'%'
		});
	};

	FilmHotspot.prototype.closeInfobox = function($infobox, $hotspot) {
		var self = this;

		self.$el.trigger('infoboxClosed');
		self.$el.trigger('wos-film-hotspot-close');

		$('html').removeClass('has-infobox-open');
		$infobox.removeClass('is-visible');
		$hotspot.removeClass('is-open');

		self.$overlay.off('click'+self.ns);
		$('.js-infobox-close').off('click'+self.ns);
		$infobox.off('click'+self.ns);
		$(window).off('keydown'+self.ns);
		$(window).off('resize'+self.ns);
		$(window).off('infoboxOpened'+self.ns);

		self.$overlay.removeClass('is-visible');

		var $video = $infobox.find('.js-infobox__video');
		if($video.length > 0) {
			// stop it
			$video[0].pause();

			var $playButton = $infobox.find('.js-infobox__video__play');
			if($playButton.length > 0) {
				$playButton.removeClass('is-hidden');
				$playButton.off(ns);
			}

			//iPad start-button workaround (otherwise it somehow won't start if loaded through world). Video has to be self toggled per controls
			if(self.isIOS) {
				//iphone workaround
				var $videoClone = $video.clone(),
					$parentContainer = $video.parent();
				$video.remove();
				$parentContainer.prepend($videoClone);

				$videoClone.attr('controls', true);
			}
		}

		if($infobox.find(".js-infobox__youtube")){
			var iFrameEle = $infobox.find(".js-infobox__youtube");
			this.resetYoutubeVideo(iFrameEle);
		}
	};

	FilmHotspot.prototype.getCenterCords = function($hotspot) {
		var self = this;

		return {
			top: $hotspot.position().top - 18,
			left: $hotspot.position().left - 18
		};
	};

	return FilmHotspot;
});


define (
'app/content/FilmSlide',[
	'jquery',
	'app/content/FilmHotspot',
	'hv/animation/AnimationFrame',
	'app/Config',
	'app/modules/GATracker'
],
function(
	$, FilmHotspot, AnimationFrame, Config, GATracker
) {

	var ns = ".filmSlide";

	var DEFAULT_OPTIONS = {
		autoplay: false
	};

	var nbrOfInstance = 0;
	var $window,
		windowHeight,
		windowWidth;

	function FilmSlide(element) {
		var self = this;

		self.$container = $(element);
		this.options = $.extend({}, DEFAULT_OPTIONS, this.$container.data('options') || {});
		self.$container.addClass("is-initiated");
		self.$el = self.$container.find('.js-video');
		self.$window = $(window);
		self.windowHeight = self.getWindowHeight();
		self.windowWidth = self.$window.width();
		self.loadedEventTriggered = false;
		self.hasRelatedMedia = self.$el.hasClass("has-related_media");

		self.$video = self.$container.find('.js-video');

		self.video = self.$container.find('.js-video')[0];
		self.videoName = self.$video.data('name');
		self.requestAnimationFrame = true;

		self.trackingData = self.$video.data('tracking');
		self.checkDelayedAutoplay();

		if(self.trackingData.hotspots.length > 0) {
			self.$hotspot = $(self.trackingData.hotspots[0].id);
		}

		self.hotspots = [];
		self.videoWidth = self.$video.width();
		self.videoHeight = self.$video.height();
		self.waiting = 0;

		self.$playButton = self.$('.js-play-button');

		if(window.location.hash && (window.location.hash).indexOf('slide=') != -1) {
			var hash = window.location.hash;
			self.startIndex = parseInt(hash.split('slide=').pop(), 10);
		}


		if(Modernizr.touch) {
			self.$playButton.on('click'+ns, self.playButtonClick);
		}

		self.resizeFilm();
		self.initHotspotTracking();

		self.$window.on('resize'+ns, $.proxy(self.onResize, this));

		self.$video.on('canplay'+ns, function(){
			self.resizeFilm();
		});

		self.$video.on('loadedmetadata'+ns, function(e) {
			self.resizeFilm();
		});

		self.initVideoControls();

		this.$container.on('slide:show'+ns, function(){
			if (this.options.autoplay) {
				this.playVideo();
			}
		}.bind(this));

		this.$container.on('slide:hide'+ns, function(){
			this.pauseVideo();
			if (this.isHotspotActive) {
				this.videoIsEnded();
			}
		}.bind(this));

		
		$('body').on('keydown'+ns, function(e) {
			if(e.keyCode === 27) {
				if(!self.isVideoStopped && $('.js-content-minimize').length) {
					e.stopPropagation();

					$('.js-content-minimize').trigger('click');
				}
			}
		});

		$('.js-content-minimize').on('click'+ns, function(e) {
			e.preventDefault();

			self.videoIsEnded();
		});

		$('body').on('shareboxOpen'+ns, function(e) {
			self.hasInfoboxOpened = true;
			self.pauseVideo();
		});

		$('body').on('shareboxClose'+ns, function(e) {
			self.hasInfoboxOpened = false;

			if (self.isHotspotFilm != self.isHotspotActive) {
				return; // ignore when it's hotspot movie but not visible
			}
			// don't autoplay on mobile
			if(self.windowWidth > 750  && self.$container.hasClass("has-video")) {
				setTimeout(function() {
					self.playVideo();
				}, 300);
			}
		});


		this.$video.on('canplaythrough'+ns, function(e) {
			if(!this.hasInfoboxOpened && this.options.autoplay && !this.isVideoStopped) {
				this.playVideo();
			}
		}.bind(this));

		self.displayControls(false);

		if($('body').hasClass('content-film-body')) {
			$('.js-content-container').addClass('is-animated');
		}

		// hack for android
		if(self.android) {
			self.$('.js-play-button').addClass('video-play-button--visible');
			$('body').on('touchstart'+ns, '.js-content-close', function() {
				$(this).trigger('click');

				if($('body').hasClass('content-film-body')) {
					window.location = $(this).attr('href');
				}
			});
		}
		// hack for iphone
		if(self.iOS) {
			$('html').addClass('is-iOS');

			self.$video.on('pause'+ns, function() {

				self.videoIsEnded();
			});
		}

		// ABO
		// self.playFromHotspot();

	}

	FilmSlide.prototype.$ = function(selector) {
		return this.$container.find(selector);
	};

	FilmSlide.prototype.android = (/android/i).test(navigator.userAgent);
	FilmSlide.prototype.iOS = /iP(ad|hone|od)/.test(navigator.userAgent);
	FilmSlide.prototype.iOS7 = (/iPad;.*CPU.*OS 7_\d/i).test(navigator.userAgent);


	FilmSlide.prototype.isActive = function() {
		return this.$container.hasClass('is-active');
	};

	FilmSlide.prototype.checkDelayedAutoplay = function() {
		var self = this;

		$('body').on('showTransitionStart.roundMask'+ns, onTransitionStart);

		function onTransitionStart() {
			self.pauseVideo({
				'displayControls' : false
			});

			$('body').on('showTransitionEnd.roundMask'+ns, onTransitionEnd);
		}
		function onTransitionEnd() {
			self.playVideo({
				'delayed' : true
			});

			$('.js-content-container').addClass('is-animated');

			$('body').off('showTransitionStart.roundMask'+ns, onTransitionStart);
			$('body').off('showTransitionEnd.roundMask'+ns, onTransitionEnd);
		}
	};

	FilmSlide.prototype.sendTrackEvent = function() {
		var self = this;

		var href = window.location.pathname+"/slide"+self.startIndex+"/"+self.videoName;
		var currentPercentage = Math.floor(self.video.currentTime * 100 / self.video.duration);
		currentPercentage = Math.floor(currentPercentage / 25) * 25; // round to 0, 25, 50, 75, 100
		if (self.lastCurrPercentage !== currentPercentage) {
			GATracker.track('send', 'event', 'video', 'play', href, currentPercentage);
			self.lastCurrPercentage = currentPercentage;
		}
	};


	FilmSlide.prototype.initVideoControls = function() {
		var self = this;
		var $progressBar = self.$('.js-progress-bar');
		var $loadingBar = self.$('.js-loading-bar');
		var $progressControl = self.$('.js-video-progress-control .progress-bar-wrapper');

		self.toggleControlsOnClick();
		if(Modernizr.touch) {
			self.updatePlayToggle(false);
		}

		self.$video.on('progress'+ns, function() {
			if(this.buffered.length >= 1) {
				var percentage = Math.ceil((this.buffered.end(0) / this.duration) * 100);

				if(percentage >= 100) {
					$loadingBar.css('display', 'none');
				} else {
					$loadingBar.css('width', percentage + '%');
				}
			}
		});

		self.$video.on('timeupdate'+ns, function(e) {
			var percentage = Math.floor((100 / self.video.duration) * self.video.currentTime);
			$progressBar.css('width', percentage + '%');

			if(self.android) {
				self.videoStartTime = new Date().getTime() - (self.video.currentTime * 1000);
			}

			if(self.hasRelatedMedia){
				if(self.video.currentTime >= self.video.duration - 7){
					self.$container.addClass('is-ending');
				}else{
					self.$container.removeClass('is-ending');
				}
			}
			self.sendTrackEvent();
		});

		// on first play (can't listen to 'play'-evt because it isn't fired when autoplay="autoplay" on the first time)
		self.$video.one('timeupdate'+ns, function(e) {
			// avoid repaints due to background on $video
			self.$video.css({
				'background' : 'none'
			});
			self.$('.js-video-poster').remove();
		});

		self.$video.on('pause'+ns, function(e) {
			self.pauseVideo({
				'displayControls' : false
			});
		});

		$progressControl.on('click'+ns, function(e) {
			e.preventDefault();

			var clickPos = e.pageX,
				totalWidth = $progressControl.outerWidth(),
				newPercentage = clickPos / totalWidth;

			self.hideAllHotspots();

			self.video.currentTime = newPercentage * self.video.duration;
			self.playVideo();

			self.$el.trigger('wos-film-progress-bar-click'+ns);
		});

		self.$video.on('waiting', function(e) {
			if(self.waiting > 0) {
				self.displayLoadingIndicator();
			}
			self.waiting += 1;
		});

		self.$('.js-video-play-toggle').on('click'+ns, function(e) {
			e.preventDefault();
			e.stopPropagation();

			var $this = $(this);

			if(self.isVideoStopped) {
				self.playVideo();
				$this.trigger('wos-film-play-click');
			} else {
				self.pauseVideo();
				$this.trigger('wos-film-pause-click');
			}

			$this.trigger('wos-film-play-toggle-click');
		});

		self.$('.js-video-mute-toggle').on('click'+ns, function(e) {
			e.stopPropagation();
			e.preventDefault();
			var $this = $(this);

			var isMuted = self.video.muted;

			if(isMuted) {
				$this.addClass('video-mute-toggle--mute').removeClass('video-mute-toggle--unmute');
				self.$('.video-mute-toggle__desc').text(Config.get('langVideoMute'));
				$this.trigger('wos-film-unmute-click');
			} else {
				$this.addClass('video-mute-toggle--unmute').removeClass('video-mute-toggle--mute');
				self.$('.video-mute-toggle__desc').text(Config.get('langVideoUnmute'));
				$this.trigger('wos-film-mute-click');
			}

			self.video.muted = !isMuted;

			$this.trigger('wos-film-mute-toggle-click');
		});

		$(document).on('keydown'+ns, function(e) {
			if ( !self.isActive() ) {
				return;
			}

			if(self.$container.hasClass("has-video")) {
				if(e.keyCode === 32) { // spacebar
					if(self.isVideoStopped) {
						self.playVideo();
					} else {
						self.pauseVideo();
					}
				}
			}
		});
	};

	FilmSlide.prototype.displayLoadingIndicator = function() {
		var self = this;

		//$('.js-video-loading').addClass('is-visible');
		self.$('.js-video-play-toggle').addClass('video-play-toggle--loading');
		self.displayControls(true);
	};

	FilmSlide.prototype.updatePlayToggle = function(isPlaying) {
		var self = this;

		isPlaying = isPlaying || !self.isVideoStopped;
		var $controls = $('.js-video-progress-control');

		if(isPlaying) {
			//play
			//$controls.removeClass('hovered');
			self.$('.js-video-play-toggle-text').text(Config.get('langVideoPause'));
			self.$('.js-video-play-toggle').addClass('video-play-toggle--pause').removeClass('video-play-toggle--play');
		} else {
			//pause
			self.$('.js-video-play-toggle-text').text(Config.get('langVideoPlay'));
			self.$('.js-video-play-toggle').addClass('video-play-toggle--play').removeClass('video-play-toggle--pause');
			//$controls.addClass('hovered');
		}
	};

	FilmSlide.prototype.displayControls = function(visible) {
		var self = this;


		var $controls = this.$('.js-video-progress-control');

		if(visible) {
			$controls.addClass('hovered');

			// hide it after n seconds
			clearTimeout(self.controlsTimeout);
			self.controlsTimeout = setTimeout(function() {
				if(self && !self.isVideoStopped) {
					self.displayControls(false);
				}
			}, 3000);
		} else {
			clearTimeout(self.controlsTimeout);
			$controls.removeClass('hovered');
		}
	};

	FilmSlide.prototype.toggleControlsOnClick = function() {
		var self = this;

		var isVisible = true;

		self.$video.on('click'+ns, function(e) {
			isVisible = !isVisible;
			self.displayControls(isVisible);
		});

		return false;
	};


	FilmSlide.prototype.playVideo = function(options) {

		var self = this;
		if ( !self.isActive() ) {
			return;
		}

		if(self.hasInfoboxOpened) {
			self.$('.js-overlay').trigger('click');
		}

		self.$('.js-video-play-toggle').removeClass('video-play-toggle--loading');

		if(options) {
			if(options.delayed) {
				return setTimeout(function() {
					startVideo(options);
				}, 500);
			}
		} else {
			startVideo(options);
		}

		function startVideo(options) {
			AnimationFrame.cancel(self.animationFrame);

			self.isVideoStopped = false;
			self.updatePlayToggle(true);
			self.$container.addClass('is-video-playing');

			self.$container.find('.js-video')[0].play();


			if(self.android) {
				self.$video.one('timeupdate'+ns, function(e) {
					self.videoStartTime = new Date().getTime() - (self.video.currentTime * 1000);
					self.animationFrame = AnimationFrame.request($.proxy(self.moveHotspots, self));
				});
			} else {
				self.animationFrame = AnimationFrame.request($.proxy(self.moveHotspots, self));
			}
			//self.$playButton.css({display: 'none'});
		}
	};

	FilmSlide.prototype.pauseVideo = function(options) {
		var self = this;

		if ( !self.isActive() ) {
			return;
		}

		self.isVideoStopped = true;
		self.updatePlayToggle(false);
		self.$container.find('.js-video')[0].pause();
		AnimationFrame.cancel(self.animationFrame);

		self.$container.removeClass('is-video-playing');

		if(options) {
			if(options.displayControls && options.displayControls === true) {
				self.displayControls(true);
			}
		} else {
			if(!self.hasInfoboxOpened && !self.isHotspotHovered) {
				self.displayControls(self.isVideoStopped);
			}
		}
	};

	FilmSlide.prototype.playButtonClick = function() {
		var self = this;

		self.$video.off('play'+ns, self.playButtonClick);
		self.$('.js-video-poster').remove();
		self.playVideo();
		self.$playButton.css({
			'display':'none'
		});
	};

	FilmSlide.prototype.onResize = function(e) {
		var self = this;

		self.windowWidth = $(window).width();
		self.windowHeight = self.getWindowHeight();

		self.resizeFilm();
	};

	FilmSlide.prototype.resizeFilm = function() {
		var self = this;

		self.windowHeight = self.getWindowHeight(); //because of ios7 bug
		self.windowWidth = $(window).width();

		var newDimensions = self.scaleFilm();

		self.videoHeight = newDimensions.height;
		self.videoWidth = newDimensions.width;

		var $videoWrapper = self.$('.js-video-wrapper');

		//if(newDimensions.scale === 'stretch') {

		//CHECK THIS AGAIN
		var marginLeft = Math.round(((self.videoWidth - self.windowWidth) / 2) * -1);
		var marginTop = Math.round(((self.videoHeight - self.windowHeight) / 2) * -1);

		$videoWrapper.css({
			'left': marginLeft,
			'top': marginTop
		});

		self.factorY = self.videoHeight / this.trackingData.sourceHeight;
		self.factorX = self.videoWidth / this.trackingData.sourceWidth;

		self.setHotspotStartPositions();
	};


	FilmSlide.prototype.scaleFilm = function() {
		var self = this;

		var aspectRatio = this.trackingData.sourceWidth / this.trackingData.sourceHeight,
			windowRation = self.windowWidth / self.windowHeight;

		var dimensions = {
			'height' : '',
			'width' : '',
			'scale' : 'none'
		};

		if(aspectRatio > windowRation) {
			dimensions.scale = 'stretch'
			dimensions.height = self.windowHeight;
			dimensions.width = Math.round(this.trackingData.sourceWidth * (self.windowHeight / this.trackingData.sourceHeight));
		} else if(aspectRatio < windowRation) {
			dimensions.scale = 'stretch'
			dimensions.height = Math.round(this.trackingData.sourceHeight * (self.windowWidth / this.trackingData.sourceWidth));
			dimensions.width = self.windowWidth;
		}

		self.$video.css(dimensions);
		return dimensions;
	};

	FilmSlide.prototype.getWindowHeight = function() {
		var self = this;
		//ios7 landscape windowHeight bug.
		if (self.iOS7) {
			window.scrollTo(0, 0);
			return window.innerHeight;
		}

		return self.$window.height();
	};


	FilmSlide.prototype.playFromHotspot = function() {
		var self = this;

		this.isHotspotFilm = true;
		this.isHotspotActive = true;


		$(".js-overlay").hide();
		self.$(".js-video-hotspot").hide();
		self.$(".js-slideshow-cover").hide();
		self.$(".js-filmSlide-infos").hide();
		$(".js-slideshow-pager").show();

		$(".js-content-close").hide();
		$(".js-content-minimize").show();

		self.video.currentTime = 0;
		self.playVideo();
	};

	FilmSlide.prototype.pauseFromSlideChanging = function() {
		var self = this;
		if(self.$container.hasClass("has-video")) {
			self.pauseVideo();
		}

	};

	FilmSlide.prototype.videoIsEnded = function(){
		var self = this;

		this.isHotspotActive = false;

		this.pauseVideo();

		if(self.activeHotspot) {
			self.hideHotspot($(self.activeHotspot.id));
		}

		$(".js-video-hotspot").show();
		$(".js-slideshow-cover").show();
		$(".js-filmSlide-infos").show();


		$(".js-content-close").show();
		$(".js-content-minimize").hide();
		AnimationFrame.cancel(self.animationFrame);
	};


	// –––––––––––––––––––––––––––––––––––––––––––

	FilmSlide.prototype.destroy = function() {
		var self = this;

		$(".js-slideshow").find(".js-video").attr("src", " ");

		$('body').off(ns);
		$(document).off(ns);
		$(window).off(ns);

		self.$el = null;
		self = null;
	};













	// TRACKED HOTSPOTS
	// ****************
	// 



	FilmSlide.prototype.initHotspotTracking = function() {
		var self = this;

		if ( !self.isActive() ) {
			return;
		}

		self.$container.find('.js-hotspot').each(function() {
			var $this = $(this);

			self.hotspots.push(new FilmHotspot($this));
		});

		self.$container.find('.js-hotspot:not(is-hidden)').on('mouseenter'+ns + ' touchstart'+ns, function() {
			if(!self.hasInfoboxOpened) {
				clearTimeout(self.timeout);
				self.isHotspotHovered = true;
				self.pauseVideo({
					'displayControls' : false
				});
			}
		});
		self.$container.find('.js-hotspot:not(is-hidden)').on('mouseleave'+ns + ' touchstart'+ns, function() {
			if(!self.hasInfoboxOpened) {
				self.isHotspotHovered = false;
				self.timeout = self.playVideo({
					'delayed' : true
				});
			}
		});

		$(document).on('infoboxOpened.filmSlide'+ns, function() {
			if ( !self.isActive() ) {
				return;
			}

			self.pauseVideo({
				'displayControls' : false
			});
			clearTimeout(self.timeout);
			self.hasInfoboxOpened = true;
			self.isHotspotHovered = true;
		});
		$(document).on('infoboxClosed.filmSlide'+ns, function() {
			if ( !self.isActive() ) {
				return;
			}
			self.hasInfoboxOpened = false;
			self.isHotspotHovered = false;

			self.timeout = self.playVideo({
				'delayed' : true
			});
		});
	};

	FilmSlide.prototype.moveHotspots = function(timestamp) {
		var self = this;
		if(self === null) return;

		var currentFrame = Math.round(self.video.currentTime * self.trackingData.fps);

		if(self.android && !self.isVideoStopped) {
			if(self.video.currentTime > 0) {
				var playedTime = (new Date().getTime() - self.videoStartTime) / 1000;
				currentFrame = Math.round(playedTime * self.trackingData.fps);
			}
		}

		// only once per frame
		if(currentFrame !== self.lastFrame) {

			if(!self.activeHotspot) {
				self.activeHotspot = self.findHotspot(currentFrame);

				if(self.activeHotspot) {
					self.$hotspot = self.$container.find(self.activeHotspot.id);
					self.halfHotspotWidth = self.$hotspot.outerWidth() / 2;
				}
			}

			var hotspot = self.activeHotspot;

			if(hotspot) {
				var hotspotCords = hotspot.frames[(currentFrame - hotspot.startFrame - 1)]; //anpassung frame

				if(hotspotCords) {
					self.setHotspotPosition(self.$hotspot, (hotspotCords.x * self.factorX - self.halfHotspotWidth), (hotspotCords.y * self.factorY - self.halfHotspotWidth));

					//check for fade out
					if(currentFrame >= (hotspot.startFrame + hotspot.frames.length - 10)) { // -5 -> fade out 5 frames früher
						self.$hotspot.addClass('is-hidden').removeClass('hotspot--tooltip-visible');
					}
				} else {
					self.activeHotspot = undefined;
				}

				self.lastFrame = self.currentFrame;
			}
		}

		self.animationFrame = AnimationFrame.request($.proxy(self.moveHotspots, self));
	};

	FilmSlide.prototype.setHotspotPosition = function($hotspot, x, y) {
		var self = this;


		if(Modernizr.csstransforms3d) {
			self.$hotspot.css({
				'-webkit-transform': 'translate3d(' + x + 'px,' + y + 'px, 0)',
				'-moz-transform': 'translate3d(' + x + 'px,' + y + 'px, 0)',
				'transform': 'translate3d(' + x + 'px,' + y + 'px, 0)'
			}).removeClass('is-hidden').addClass('hotspot--tooltip-visible');
		} else if(Modernizr.csstransforms) {
			self.$hotspot.css({
				'transform': 'translate(' + x + 'px,' + y + 'px)'
			}).removeClass('is-hidden').addClass('hotspot--tooltip-visible');
		} else {
			self.$hotspot.css({
				'top' : y,
				'left' : x
			}).removeClass('is-hidden').addClass('hotspot--tooltip-visible');
		}
	};

	FilmSlide.prototype.hideAllHotspots = function() {
		var self = this;

		this.$('.js-hotspot').removeClass('hotspot--tooltip-visible').addClass('is-hidden');
	};

	FilmSlide.prototype.findHotspot = function(currentFrame) {
		var self = this;
		var hotspots = this.trackingData.hotspots;

		for (var i = hotspots.length - 1; i >= 0; i--) {
			var hotspot = hotspots[i];

			if(hotspot.startFrame + 2 == currentFrame) { // delayed fade in -> hotspot.startFrame + 5
				return hotspot;
			} else if(hotspot.startFrame + 2 <= currentFrame && (hotspot.startFrame + hotspot.frames.length) > currentFrame) { // delayed fade in -> hotspot.startFrame + 5
				return hotspot;
			}
		}
	};


	FilmSlide.prototype.setHotspotStartPositions = function() {
		var self = this;

		var i;

		for (i = this.trackingData.hotspots.length - 1; i >= 0; i--) {
			var hotspot = this.trackingData.hotspots[i],
				$hotspot = $(hotspot.id),
				hotspotCords = hotspot.frames[0];

			$hotspot.css({
				'-webkit-transform': 'translate3d(' + (hotspotCords.x * self.factorX - 20) + 'px,' + (hotspotCords.y * self.factorY - 20) + 'px, 0)',
				'-moz-transform': 'translate3d(' + (hotspotCords.x * self.factorX - 20) + 'px,' + (hotspotCords.y * self.factorY - 20) + 'px, 0)',
				'transform': 'translate3d(' + (hotspotCords.x * self.factorX - 20) + 'px,' + (hotspotCords.y * self.factorY - 20) + 'px, 0)'
			});
		}
	};

	FilmSlide.prototype.hideHotspot = function($hotspot) {
		$hotspot.addClass('is-hidden').removeClass('hotspot--tooltip-visible');
	};



	return FilmSlide;
});

define (
'app/content/GyroParallax',[
	'jquery'
],
function(
	$
) {
	var ns = '.gyro-parallax';
	var self,
		$el;

	var maxMove = 10;

	/*var scaleInPx,
		scale;*/

	function GyroParallax($element) {
		this.$el = $element;
		self = this;

		this.initGyroListener();


		this.$window = $(window);

		this.windowHeight = this.$window.height();
		this.windowWidth = this.$window.width();

		/*scaleWidthInPx = (this.$el.width() * 1.3) - this.$el.width();
		scaleHeightInPx = (this.$el.height() * 1.3) - this.$el.height();

		// console.log(scaleHeightInPx);*/

		return this;
	}

	GyroParallax.prototype.init = function($element) {
		// body...
	};

	GyroParallax.prototype.initGyroListener = function() {
		var self = this;

		if(Modernizr.csstransforms3d) {
			// deviceorientation-parallax if products page is viewed on iPad (android performance...)
			if(navigator.userAgent.match(/(iPad|iPhone|iPod)/g)) {
				$(window).on('deviceorientation'+ns, this.deviceorientationHandler);
			} else {
				$(window).on('mousemove'+ns, this.mousemoveHandler);
			}
		}
	};

	GyroParallax.prototype.mousemoveHandler = function(e) {
		var x = e.clientX,
			y = e.clientY;

		var cloudOffsetX = ((x - (self.windowWidth / 2)) / self.windowWidth)  * maxMove * -1,
			cloudoffsetY = ((y - (self.windowHeight / 2)) / self.windowHeight) * maxMove * -1;

		self.$el.css({
			'transform' : 'translate3d(' + cloudOffsetX + 'px, ' + cloudoffsetY + 'px, 0) scale(1.3)'
		});
	};

	GyroParallax.prototype.deviceorientationHandler = function(e) {
		e = e.originalEvent;

		var betta, gamma;

		if (window.orientation !== null) {
			var screenOrientation = window.orientation;

			if (screenOrientation === -90 || screenOrientation == 90) { // landscape
				beta = e.beta;
				gamma = e.gamma;
			} else { // portrait
				beta = e.gamma;
				gamma = e.beta;
			}
		}

		beta =  Math.round(beta);
		gamma = Math.round(gamma / 2.5);

		if(beta > 40) {
			beta = 40;
		} else if(beta < -40) {
			beta = -40;
		}

		if(gamma > 40) {
			gamma = 40;
		} else if(gamma < -40) {
			gamma = -40;
		}

		self.$el.css({
			'transform' : 'translate3d(' + beta + 'px, ' + gamma + 'px, 0) scale(1.3)',
			'transition' : 'all 50ms'
		});

	};

	GyroParallax.prototype.degToRad = function(value) {
		return value / (Math.PI / 180);
	};

	GyroParallax.prototype.destroy = function() {
		$(document).off(ns);
		$(window).off(ns);
		self = null;
	};

	return GyroParallax;
});

/**
 * Slide events:
 * slide:visibilitychange
 * slide:show
 * slide:hide
 */


define (
'app/content/Slideshow',[
	'jquery',
	'app/util/Utils',
	'app/content/Hotspot',
	'app/content/FilmSlide',
	'app/content/GyroParallax',
	'app/modules/GATracker',
	'mousewheel'
],
function(
	$,
	Utils,
	Hotspot,
	FilmSlide,
	GyroParallax,
	GATracker
) {
	var ns = '.slideshow';

	var IS_IOS7IPad = navigator.userAgent.match(/iPad;.*CPU.*OS 7_\d/i);
	var IS_IOS7IPhone = navigator.userAgent.match(/iPhone;.*CPU.*OS 7_\d/i);
	var IS_IOS = /iP(ad|hone|od)/.test(navigator.userAgent);



	var options = {
		duration: 3000,
		speed: 400,
		infiniteLoop: true,
		slidesSelector: '.js-slideshow-slide',
		autoShow: false,
		carousel: true,
		startingSlide: 1,
		keyControl: true,
		pager: true,
		mousewheelControl : true
	};

	function Slideshow(element) {
		var self = this;

		this.$el = $(element || '.js-slideshow');
		this.$slides = this.$el.find(options.slidesSelector);
		this.$backgroundImages = $('.js-slideshow-cover, .hotspot-container--products');
		this.$pagers = [];
		this.hotspots = [];


		this.childModules = [];
		this.videos = [];

		this.filmSlide = null;

		this.$window = $(window);
		this.windowHeight = window.innerHeight || this.$window.height();
		this.windowWidth = this.$window.width();

		this.isMobile = this.$window.width() <= 750;

		//ios7 landscape windowHeight bug.
		if (IS_IOS7IPhone ||
			IS_IOS7IPad) {
			window.scrollTo(0, 0);
			this.windowHeight = window.innerHeight;
		}

		this.CSS_TRANSFORMS = ((Modernizr.csstransforms3d) && (Modernizr.csstransitions)) || false;


		this.slidesTotal = this.$slides.length;
		this.lastSlideIndex = this.slidesTotal - 1;

		if(this.slidesTotal <= 1) {
			options.pager = false;
			options.autoShow = false;
			options.mousewheelControl = false;
		}

		if(options.pager) {
			this.createPager();
		}

		if(options.autoShow) {
			this.startAutoshow();
		}

		if(options.keyControl) {
			this.initKeyboardControl();
		}

		if(options.mousewheelControl) {
			this.initMousewheelListener();
		}

		if(Modernizr.touch) {
			options.speed = 300;
			this.initTouchControl();
		}



		this.initResizeListener();

		this.resizeAllBackgrounds();
		this.positionSlides();
		this.initializeHotspots();
		this.initializeVideoSlides();
		this.positionSlides();

		if(this.CSS_TRANSFORMS) {
			this.$el.css({
				'transform' : 'translate3d(0,' + -this.currentSlideIndex * this.windowHeight + 'px,0)',
				'transition' : 'none'
			});
		} else {
			this.$el.css({
				'top' : -this.currentSlideIndex * this.windowHeight
			});
		}
		this.checkLoaded();

		this.$el.on('click'+ns, '.js-content-close', function(e) {
			// mobile fix.
			window.scrollTo(0, 0);

			$(this).trigger('wos-contentclose-click');

			// to speed up roundmask hide transition
			$('.slideshow__slide:not(.is-active)').css({
				'display' : 'none'
			});
		});

		this.initRouteNetworkLinks();

		this.onOpenedFromWorld();

		if($('body').hasClass('content-slideshow-body')) {
			$('.js-content-container').addClass('is-animated');
		}

		this.$el.on('click'+ns, '.js-infobox__mobile-link', function(e) {
			var $this = $(this);
			self.openInfobox($this);

			return false;
		});

		var $gyroParallaxEl = $('.js-gyro-parallax');

		if($gyroParallaxEl.length > 0) {
			this.childModules.push(new GyroParallax($gyroParallaxEl));
		}


		$('html').removeClass('is-not-loaded').addClass('is-loaded');

		if(IS_IOS) {
			$('html').addClass('is-iOS');
		}

		this.$el.on('click'+ns, '.js-infobox__video__enlarge', $.proxy(this.onVideoEnlargeClick));



		// initial slides
		
		var startIndex = Utils.getParameterByName('slide');
		if (startIndex) {
			startIndex = parseInt(startIndex, 10);
		} else {
			startIndex = options.startingSlide - 1;
		}

		// autoplay
		var playVideo =  false;
		var autoplay = Utils.getParameterByName("autoplay");
		if( autoplay === "1"){
			playVideo = true;
		}

		this.goToSlide(startIndex, playVideo);
	}

	Slideshow.prototype.onVideoEnlargeClick = function() {

	};


	Slideshow.prototype.destroy = function() {
		var self = this;
		$('html').removeClass('content-products');

		for (var i = this.childModules.length - 1; i >= 0; i--) {
			var destroyFunction = this.childModules[i].destroy;

			if($.isFunction(destroyFunction)) {
				destroyFunction.call();
			}
		}

		$('body').off(ns);
		$(document).off(ns);
		$(window).off(ns);

		self = null;
	};

	/**
	 * Checks if first 3 slideshow-images (without tooltips imgs) are loaded and triggers a content.loaded event.
	 */
	Slideshow.prototype.checkLoaded = function() {
		var self = this;
		var $imgs = self.$el.find('img.js-slideshow-cover-bg:lt(3)'),
			imgTotal = $imgs.length;

		if(imgTotal === 0) {
			self.$el.trigger('content.loaded');
		}

		$imgs.each(function(i, img) {
			var image = new Image();

			$(image).on('load'+ns + ' error' + ns, function() {
				imgTotal -= 1;

				if(imgTotal === 0) {
					// console.log('Slideshow: all images loaded');
					self.$el.trigger('content.loaded');
				}

				$(this).off(ns);
			});

			image.src = img.src;
		});
	};

	Slideshow.prototype.initResizeListener = function() {
		var self = this;
		self.$window.on('resize'+ns, function(e) {
			self.windowHeight = window.innerHeight || self.$window.height();
			self.windowWidth = self.$window.width();
			this.isMobile = self.windowWidth <= 750;

			//ios7 landscape windowHeight bug.
			if (IS_IOS7IPhone ||
				IS_IOS7IPad) {
				window.scrollTo(0, 0);
				self.windowHeight = window.innerHeight;
			}

			// force click to close open slides
			self.$currentSlide.trigger('click');

			self.positionSlides();
			//self.positionHotspots();

			self.resizeAllBackgrounds();

			self.$el.css({
				'height' : self.windowHeight,
				'width' : self.windowWidth,
				'max-height' : self.windowHeight,
				'max-width' : self.windowWidth,
			});

			if(self.CSS_TRANSFORMS) {
				self.$el.css({
					'transform' : 'translate3d(0,' + -self.currentSlideIndex * self.windowHeight + 'px,0)',
					'transition' : 'none'
				});
			} else {
				self.$el.css({
					'top' : -self.currentSlideIndex * self.windowHeight
				});
			}
		});

		/**
		 * Debounced windows resize listener. Will postpone its execution until after 100 milliseconds have elapsed since the
		 * last time it was invoked.
		 */
		self.$window.on('resize'+ns, self._debounce(function(e) {
			for (var i = 0, len = self.hotspots.length; i <len; i++) {
				self.hotspots[i].positionTooltip();
			}

		}, 100));

	};

	Slideshow.prototype.onOpenedFromWorld = function() {
		var self = this;
		$('body').on('showTransitionStart.roundMask'+ns, onTransitionStart);

		if($('body').hasClass('content-slideshow-body')) {
			if($('.slideshow__slide--products').length >= 1) {
				$('html').addClass('content-products');
			}
		}

		function onTransitionStart() {
			// to speed up roundmask transition
			$('.slideshow__slide:not(.is-active)').css({
				'display' : 'none'
			});

			$('body').on('showTransitionEnd.roundMask'+ns, onTransitionEnd);
		}
		function onTransitionEnd() {
			$('.slideshow__slide').css({
				'display' : ''
			});
			$('.js-content-container').addClass('is-animated');


			$('body').off('showTransitionStart.roundMask'+ns, onTransitionStart);
			$('body').off('showTransitionEnd.roundMask'+ns, onTransitionEnd);

			// check if it's the product page (workaround for scrolling on mobile...)
			if($('.slideshow__slide--products').length >= 1) {
				$('html').addClass('content-products');
			}

			if(IS_IOS) {
				var $infoboxVideos = $('.js-infobox__video');

				for (var i = $infoboxVideos.length - 1; i >= 0; i--) {
					var $video = $infoboxVideos.eq(i),
						$videoClone = $video.clone(),
						$videoContainer = $video.parent();
					$video.remove();
					$videoContainer.prepend($videoClone);
				}
			}
		}
	};

	Slideshow.prototype.canScroll = function(direction){
		var self = this;
		if ( !this.$currentSlide.hasClass('has-scroll') ) {
			return true;
		}
		if ((new Date() - this.couldNotScrollAt) < 1000) {
			return false; // wait before moving to another screen when user scrolled within slide
		}
		var slideEl = this.$currentSlide.get(0);
		var slideHeight = slideEl.clientHeight;
		var slideScrollHeight = slideEl.scrollHeight;
		var slideScrollTop = slideEl.scrollTop;

		var result;
		if ( direction == 'down' ) {
			result = (slideScrollTop + slideHeight) >= (slideScrollHeight - 10);
		} else
		if ( direction == 'up' ) {
			result = slideScrollTop <= 10;
		}
		if (!result) {
			this.couldNotScrollAt = new Date();
		}

		return result;
	};

	Slideshow.prototype.initMousewheelListener = function() {
		var self = this;
		var lastScroll = new Date().getTime();

		this.$el.on('mousewheel'+ns, mousewheelHandler);

		function mousewheelHandler(e, delta) {
			if(self.isMobile && $('html').hasClass('has-infobox-open') || self.$el.hasClass('is-scroll-disabled')) {
				return;
			}

			if(lastScroll + 1000 < new Date().getTime()) {
				if(e.originalEvent.wheelDelta > 30 || delta >= 1 || (/firefox/i.test(navigator.userAgent) && delta >= 1)) { //20
					//scrolling up
					if ( self.canScroll('up') ) {
						self.goToPreviousSlide(true);
						lastScroll = new Date().getTime();
					}
				} else if(e.originalEvent.wheelDelta < -30 || delta <= -1 || (/firefox/i.test(navigator.userAgent) && delta <= -1)) { //20
					//scrolling down
					if ( self.canScroll('down') ) {
						self.goToNextSlide(true);
						lastScroll = new Date().getTime();
					}
				}
			}
		}
	};

	Slideshow.prototype.positionSlides = function() {
		var self = this;
		self.$slides.each(function(i) {
			var $this = $(this);

			$this.css({
				'top': self.windowHeight * i,
				'height': self.windowHeight
			});
		});

		self.$el.css({
			'height' : self.slidesTotal * self.windowHeight
		});
	};

	Slideshow.prototype.startAutoshow = function() {
		var self = this;
		// console.log('startAutoSlideshow');
		// clear existing intervals
		clearInterval(self.interval);

		self.interval = self.getAutoshowInterval();
	};

	Slideshow.prototype.getAutoshowInterval = function() {
		var self = this;
		return setInterval(function() {
			self.goToNextSlide();
		}, options.duration);
	};

	Slideshow.prototype.resetVideosInSlide = function($slide) {
		var $yt = $slide.find(".js-infobox__youtube");

		if($yt.length > 0){
			var iFrameEls = $yt;

			for (var i = 0; i < iFrameEls.length; i++) {
				this.resetYoutubeVideo(iFrameEls.eq(i));
			}
		}
	};

	Slideshow.prototype.goToSlide = function(index, playVideo) {
		var self = this;
		var $slide = self.getSlideByIndex(index),
			$lastSlide = self.$currentSlide;


		if ($lastSlide) {
			if ($lastSlide.is($slide)) {
				// moving to same slide makes no sense
				return;
			}

			this.resetVideosInSlide($lastSlide);

			if(self.slidesTotal > 1 && index !== self.currentSlideIndex) {
				self.fadeOutLastSlideContent($lastSlide);
			}

			$lastSlide.trigger('slide:hide');
			$lastSlide.trigger('slide:visibilitychange');
		}

		self.pauseVideoSlideChanging();

		$slide.css({
			display: '' // initially we hide all slides except the first one
		});
		$slide.addClass('is-active');
		$slide.trigger('slide:show');
		$slide.trigger('slide:visibilitychange');


		var posY = $slide.position().top;

		self._moveTop(self.$el, posY * -1);

		self.$currentSlide = $slide;
		self.currentSlideIndex = index;

		if(options.pager) {
			$('.js-slideshow-pager a.is-active').removeClass('is-active');
			var $activePager = self.$pagers[self.currentSlideIndex].find('a').addClass('is-active');
			var $activePagerCircle = $('.active-pager-circle');
			$activePagerCircle.css({
				'top' : $activePager.position().top,
				'transition' : 'all ' +  options.speed + 'ms linear'
			});
		}

		self.fadeInContent();


		if(options.autoShow) {
			// reset interval
			self.startAutoshow();
		}

		if($slide.hasClass('has-infobox-open')) {
			$slide.trigger('click');
			
		}
		$('html').removeClass('has-infobox-open');
		self.$currentHotspot = undefined;

		// play Video if the parameter is given
		if(playVideo){
			$videoHotspot = $slide.find(".js-video-hotspot");
			if($videoHotspot.length > 0) $videoHotspot.trigger('click');
		}

		GATracker.replaceLocation('#slide=' + self.currentSlideIndex, 'Slide', true);
	};

	Slideshow.prototype.fadeOutLastSlideContent = function($lastSlide) {
		var self = this;
		var previousSlideIndex = self.currentSlideIndex;
		function fadeOut(e) {
			var propertyName = e.originalEvent.propertyName,
				target = e.target.className;

			if(previousSlideIndex !== self.currentSlideIndex && (propertyName === '-webkit-transform' || propertyName === 'transform') && target.indexOf('js-slideshow') != -1) {
				$lastSlide.removeClass('is-active fade-in-end');
				self.$el.off('webkitTransitionEnd'+ns+' transitionend'+ns+' transitionEnd'+ns+' msTransitionEnd'+ns+' oTransitionEnd', fadeOut);
			}
		}

		if(self.CSS_TRANSFORMS) {
			// remove classes as soon as it is out of the view.
			self.$el.on('webkitTransitionEnd'+ns+' transitionend'+ns+' transitionEnd'+ns+' msTransitionEnd'+ns+' oTransitionEnd', fadeOut);
		} else {
			$lastSlide.removeClass('is-active fade-in-end');
		}
	};

	Slideshow.prototype.fadeInContent = function() {
		var self = this;
		function fadeInEnd(e) {
			e.stopPropagation();

			var propertyName = e.originalEvent.propertyName;
			if(propertyName === '-webkit-transform' || propertyName === 'transform') {
				self.$currentSlide.addClass('fade-in-end');
				self.$currentSlide.off('webkitTransitionEnd'+ns+' transitionend'+ns+' transitionEnd'+ns+' msTransitionEnd'+ns+' oTransitionEnd', fadeInEnd);
			}
		}

		if(self.CSS_TRANSFORMS) {
			self.$currentSlide.on('webkitTransitionEnd'+ns+' transitionend'+ns+' transitionEnd'+ns+' msTransitionEnd'+ns+' oTransitionEnd', fadeInEnd);
		} else {
			self.$currentSlide.addClass('fade-in-end');
		}

	};

	Slideshow.prototype._moveTop = function($el, top) {
		var self = this;
		if(self.CSS_TRANSFORMS) {
			$el.css({
				'transform' : 'translate3d(0,' + top + 'px,0)',
				'transition' : 'all ' + options.speed + 'ms ease-out'
			});
		} else {
			$el.stop().animate({
				'top': top
			}, {
				duration : options.speed,
				easing : 'linear'
			});
		}
	};

	Slideshow.prototype.goToNextSlide = function(isTouch) {
		var self = this;
		isTouch = isTouch || false;

		var nextSlideIndex = parseInt(self.currentSlideIndex, 10) + 1;

		if(nextSlideIndex > self.lastSlideIndex) {
			if(options.carousel && !isTouch) {
				nextSlideIndex = 0;
			} else {
				nextSlideIndex = self.lastSlideIndex;
			}
		}

		self.goToSlide(nextSlideIndex);
	};

	Slideshow.prototype.goToPreviousSlide = function(isTouch) {
		var self = this;
		var nextSlideIndex = self.currentSlideIndex - 1;

		if(nextSlideIndex < 0) {
			if(options.carousel && !isTouch) {
				nextSlideIndex = self.lastSlideIndex;
			} else {
				nextSlideIndex = 0;
			}
		}

		self.goToSlide(nextSlideIndex);
	};

	Slideshow.prototype.goToFirstSlide = function() {
		var self = this;
		self.goToSlide(0);
	};

	Slideshow.prototype.goToLastSlide = function() {
		var self = this;
		self.goToSlide(self.lastSlideIndex);
	};

	Slideshow.prototype.stopAutoshow = function() {
		var self = this;
		clearInterval(self.interval);
	};

	Slideshow.prototype.getSlideByIndex = function(index) {
		var self = this;
		return self.$slides.eq(index);
	};

	Slideshow.prototype.initTouchControl = function() {
		var self = this;
		if(self.slidesTotal > 1) {
			var $slide,
				touchStartY,
				parentStartY,
				slideStartY,
				touchStartTime;


			var slideEl,
			    maxScroll,
			    slideScrollTop;

			self.$el.on('touchstart'+ns, onTouchStart);

			function onTouchStart(e) {
				if(self.isMobile && $('html').hasClass('has-infobox-open') || self.$el.hasClass('is-scroll-disabled')) {
					return;
				}

				var touches = e.originalEvent.touches[0];

				$slide = self.$currentSlide; //$(e.target).closest('.js-slideshow-slide');

				touchStartY = touches.pageY;
				parentStartY = self.currentSlideIndex * self.$currentSlide.height() * -1;
				slideStartY = self.currentSlideIndex * self.$currentSlide.height();

				slideEl = $slide.get(0);
				maxScroll =  slideEl.scrollHeight - slideEl.clientHeight;
				slideScrollTop = slideEl.scrollTop;

				touchStartTime = new Date().getTime();

				self.$el.on('touchmove'+ns, onTouchMove);
				self.$el.on('touchend'+ns, onTouchEnd);

				self.$el.off('touchstart'+ns, onTouchStart);
			}

			function onTouchMove(e) {
				e.preventDefault();

				var touches = e.originalEvent.touches[0];

				var touchDistance = (touches.pageY - touchStartY);

				var scrollTop = slideScrollTop;
				if ( touchDistance > 0 && maxScroll > 0 ) {
					scrollTop -= touchDistance;
					if ( scrollTop < 0 ) {
						touchDistance = -scrollTop;
						scrollTop = 0;
					} else {
						touchDistance = 0;
					}
				}
				if ( touchDistance < 0 && maxScroll > 0 ) {
					scrollTop -= touchDistance;
					if ( scrollTop > maxScroll ) {
						touchDistance = maxScroll - scrollTop;
						scrollTop = maxScroll;
					} else {
						touchDistance = 0;
					}
				}

				slideEl.scrollTop = scrollTop;

				// slide last and first a bit slower
				if(($slide.is(':last-child') && (touchStartY > touches.pageY)) || ($slide.is(':first-child') && (touchStartY < touches.pageY))) {
					touchDistance = touchDistance / 3;
				}

				if(self.CSS_TRANSFORMS) {
					self.$el.css({
						'transform' : 'translate3d(0,' + (touchDistance - slideStartY) + 'px,0)',
						'transition' : 'none'
						//'top' : touchDistance - slideStartY
					});
				} else {
					self.$el.css({
						'top' : touchDistance - slideStartY
					});
				}
			}

			function onTouchEnd(e) {
				var slideAbsPosition = self.$el.position().top,
					relSlidePosY = (slideAbsPosition - parentStartY),
					touchDuration = (new Date().getTime() - touchStartTime),
					touches = e.originalEvent.changedTouches[0],
					touchDistance = touches.pageY - touchStartY;

				if ( Math.abs(relSlidePosY) === 0 ) {
					// do nothing
				} else
				if(Math.abs(relSlidePosY) < self.windowHeight / 3 && touchDuration > 200) {
					//move back to start position
					self._moveTop(self.$el, parentStartY);
				} else if(touchDistance < 20 && touchDistance > -20) {
					//make sure vertical touchDistance is at least 20px
					self._moveTop(self.$el, parentStartY);
				} else if(touchStartY < touches.pageY) {
					// move to previous
					self.goToPreviousSlide(true);
				} else if(touchStartY > touches.pageY){
					// move to next
					self.goToNextSlide(true);
				}

				self.$el.off('touchmove'+ns, onTouchMove);
				self.$el.off('touchend'+ns, onTouchEnd);
				self.$el.on('touchstart'+ns, onTouchStart);
			}
		}
		/*} else {
			self.$el.on('touchstart', function(e) {
				e.preventDefault();
			});
		}*/
	};

	Slideshow.prototype.initKeyboardControl = function() {
		var self = this;
		$(document).on('keyup'+ns, function(e) {
			switch(e.keyCode) {
				case 37:	self.openPreviousHotspot(); //left
							break;
				case 38:	self.goToPreviousSlide(); //up
							break;
				case 39:	self.openNextHotspot(); //right
							break;
				case 40:	self.goToNextSlide(); //down
							break;
				case 36:	self.goToFirstSlide(); // home
							break;
				case 35:	self.goToLastSlide(); // end
							break;
				case 33:	self.goToFirstSlide(); //pageUp
							break;
				case 34:	self.goToLastSlide(); //pageDown
							break;
			}
		});
	};

	/**
	 * openNextHotspot & openPreviousHotspot gets the next/prev hotspot based on the dom position.
	 */
	Slideshow.prototype.openNextHotspot = function() {
		var self = this;
		if(self.$currentHotspot) {
			self.$currentHotspot = self.$currentHotspot.next('.js-img-hotspot');

			if(self.$currentHotspot.length === 0) {
				self.$currentSlide.trigger('click');
				self.$currentHotspot = undefined;
				return false;
			}
		} else {
			self.$currentHotspot = self.$currentSlide.find('.js-img-hotspot').first();
		}

		self.$currentHotspot.trigger('click');
	};

	Slideshow.prototype.openPreviousHotspot = function() {
		var self = this;
		if(self.$currentHotspot) {
			self.$currentHotspot = self.$currentHotspot.prev('.js-img-hotspot');

			if(self.$currentHotspot.length === 0) {
				self.$currentSlide.trigger('click');
				self.$currentHotspot = undefined;
				return false;
			}
		} else {
			self.$currentHotspot = self.$currentSlide.find('.js-img-hotspot').last();
		}

		self.$currentHotspot.trigger('click');
	};

	Slideshow.prototype.sortHotspotsByCoordinates = function() {
		var self = this;
		var $hotspotList = self.$currentSlide.find('.js-img-hotspot');

		$hotspotList.sort(function($a, $b) {
			var aPos = $.data($a, 'position');
			var bPos = $.data($b, 'position');

			if(aPos && bPos) {
				if(aPos[0] > bPos[0]) {
					return 1;
				}
				if(bPos[0] > aPos[0]) {
					return -1;
				}

				return 0;
			}
		});

		return $hotspotList;
	};

	/**
	 * Creates Slideshow Pager
	 */
	Slideshow.prototype.createPager = function() {
		var self = this;
		var $pagerWrapper = $('<ol class="js-slideshow-pager slideshow__pager slideshow__pager--light"></ol>');

		// create a Pager per Slide
		for(var i = 1; i <= self.slidesTotal; i++) {
			var $pager;

			if(i === options.startingSlide) {
				$pager = $('<li><a href="#" class="slideshow__pager__link is-active" data-slide="' + i + '">Slide ' + i + '</a></li>');
			} else {
				$pager = $('<li><a href="#" class="slideshow__pager__link" data-slide="' + i + '"> ' + i + '</a></li>');
			}

			$pagerWrapper.append($pager);

			self.$pagers.push($pager);
		}

		$pagerWrapper.append($('<li class="active-pager-circle"></li>'));

		$('.js-slideshow-container').append($pagerWrapper);
		
		$pagerWrapper.on('click'+ns, 'a[data-slide]', this.onPagerClick.bind(this));
		this.$el.on('click'+ns, 'a[data-slide]', this.onPagerClick.bind(this));
	};

	Slideshow.prototype.onPagerClick = function(e) {
		var self = this;

		e.preventDefault();
		var slideID = parseInt($(e.currentTarget).data('slide'), 10) - 1;

		self.goToSlide(slideID);

		//resetAutoshowInterval();
		//stopAutoshow();
		$(this).trigger('wos-slideshow-pager-click');
	};

	Slideshow.prototype.initializeHotspots = function() {
		var self = this;
		for (var i = 0, len = self.$slides.length; i < len; i++) {
			var $slide = $(self.$slides[i]),
				$hotspots = $slide.find('.js-img-hotspot'),
				$bgImg = $slide.find('.js-slideshow-cover-bg');

			var sourceHeight = $bgImg.data('source-height') || 1920,
				sourceWidth = $bgImg.data('source-width') || 1080;

			for(var j = 0, jLen = $hotspots.length; j < jLen; j++) {
				var $hotspot = $($hotspots[j]);

				// save in in a array?
				self.hotspots.push(new Hotspot($hotspot, sourceHeight, sourceWidth));
			}
		}

		self.$el.on('click', '.js-img-hotspot:not(.js-video-hotspot)', function(e) {
			e.preventDefault();

			var $hotspot = $(e.target).closest('.js-img-hotspot');

			if(!$hotspot.hasClass('is-open')) {
				self.$currentHotspot = $hotspot;
				self.openInfobox($hotspot);
				$hotspot.trigger('wos-slideshow-hotspot-open');
			} else {
				var $infobox = $($hotspot.attr('href'));
				var $slide = $hotspot.closest('.js-slideshow-slide');

				self.closeInfobox($infobox, $slide, $hotspot);
				$hotspot.trigger('wos-slideshow-hotspot-close');
			}

			return false;
		});
	};

	Slideshow.prototype.openInfobox = function($hotspot) {
		var self = this;

		$('.js-infobox').removeClass('is-visible');

		var $infobox = $($hotspot.attr('href'));
		var $slide = $hotspot.closest('.js-slideshow-slide');


		self.positionInfobox($infobox, $hotspot);

		$slide.addClass('has-infobox-open');

		// workaround to disable controls etc... otherwise I would have had to refactor the dom.
		$('html').addClass('has-infobox-open');

		if(options.autoShow) {
			self.stopAutoshow();
		}
		$infobox.addClass('is-visible');


		$('.js-img-hotspot').removeClass('is-open');
		$hotspot.addClass('is-open');

		// add close listener
		$slide.one('click'+ns, function(e) {
			if ( $infobox.is(e.target) || $(e.target).parents().is($infobox) ) {
				return; // don't close when click originates from infobox
			}
			self.closeInfobox($infobox, $slide, $hotspot);
		});

		$infobox.find('.js-infobox-close').one('click'+ns, function(e) {
			// $slide.trigger('click');
			self.closeInfobox($infobox, $slide, $hotspot);
		});

		var $infoboxVideo = $infobox.find('.js-infobox__video');

		if($infoboxVideo.length > 0) {
			var infoboxVideo = $infoboxVideo[0];

			if(self.windowWidth > 750) { //don't autoplay on mobile
				setTimeout(function() {
					infoboxVideo.load();
					
					var $playButton = $infoboxVideo.parent().find('.js-infobox__video__play');

					if($playButton.length > 0) {
						$playButton.one('click'+ns, function(e) {
							e.preventDefault();
							e.stopPropagation();
							$playButton.addClass('is-hidden');
							infoboxVideo.play();
						});
					} else {
						infoboxVideo.play();
					}

					$infoboxVideo.removeAttr('controls');

					if(IS_IOS) {
						$infoboxVideo.on('timeupdate'+ns, function(e) {
							$infoboxVideo.removeAttr('controls');
							$infoboxVideo.off('timeupdate');
						});
					}
				}, 200); //opening transition
			} else {
				$infobox.on('click'+ns, '.js-infobox__video__poster', function(){
					infoboxVideo.play();
				});
			}
		}


		self.$window.one('keydown'+ns+' closeInfobox'+ns, function(e) {
			if(e.keyCode === 27) {
				self.closeInfobox($infobox, $slide, $hotspot);
			}
		});
};

	/*Slideshow.prototype.closeAllInfoboxes = function($slide) {
		($slide.find('.js-infobox')).each(function() {
			self.closeInfobox($(this), $slide);
		});
	};*/

	Slideshow.prototype.positionInfobox = function($infobox, $hotspot) {
		var self = this;
		var margin = 30;
		var $infoboxArrow = $infobox.find('.infobox__arrow');

		var $videoContainer = $infobox.closest('.js-slideshow-container'),
			parentOffset = $videoContainer.offset();

		var hotspotPos = {
			'x' : $hotspot.offset().left + ($hotspot.outerWidth() / 2) - parentOffset.left,
			'y' : $hotspot.offset().top + ($hotspot.outerHeight() / 2) - parentOffset.top
		};

		var xPos = hotspotPos.x + margin,
			yPos = hotspotPos.y - ($infobox.outerHeight() / 2);

		// and the same horizontally
		if((xPos + $infobox.outerWidth()) >= self.windowWidth - margin) {
			// position infobox on the left of hotspot
			xPos = $hotspot.offset().left - $infobox.outerWidth() - margin;
			$infoboxArrow.addClass('infobox__arrow--right').removeClass('infobox__arrow--left');
			$infobox.removeClass('infobox--right').addClass('infobox--left');
		} else {
			xPos = $hotspot.offset().left + $hotspot.outerWidth() + margin;
			$infoboxArrow.addClass('infobox__arrow--left').removeClass('infobox__arrow--right');
			$infobox.removeClass('infobox--left').addClass('infobox--right');
		}

		// position infobox vertically
		if(yPos < margin) {
			// move it a bit down
			yPos = margin;
		} else if((yPos + $infobox.outerHeight()) + margin > self.windowHeight) {
			yPos = self.windowHeight - $infobox.outerHeight() - margin;
		}

		$infobox.css({
			'top' : Math.round(yPos),
			'left' : Math.round(xPos),
			'max-height' : self.windowHeight
		});

		var infoboxArrowTop = hotspotPos.y - yPos;
		//(self.getHotspotCenterCords($hotspot).top - yPos) + ($infoboxArrow.outerHeight() / 2);
		$infoboxArrow.css({
			'top' : infoboxArrowTop
		});

		$infobox.css({
			'transform-origin': ($infobox.hasClass('infobox--left') ? 'right ' : 'left ') + (infoboxArrowTop + $infoboxArrow.outerHeight() / 2) / $infobox.outerHeight() * 100 +'%'
		});
	};

	Slideshow.prototype.getHotspotCenterCords = function($hotspot) {
		var self = this;
		var halfHotspotWidth = ($hotspot.innerWidth() / 2),
			halfHotspotHeight = ($hotspot.innerHeight() / 2);

		return {
			top: $hotspot.offset().top + halfHotspotHeight,
			left: $hotspot.offset().left + halfHotspotWidth
		};
	};

	Slideshow.prototype.closeInfobox = function($infobox, $slide, $hotspot) {
		var self = this;
		console.log('closeInfobox');
		$infobox.removeClass('is-visible');
		$slide.removeClass('has-infobox-open');
		$('html').removeClass('has-infobox-open');
		$hotspot.removeClass('is-open');

		//$target.closest('.js-slideshow-slide').removeClass('slideshow__slide--blured');
		$slide.trigger('closeInfobox'+ns);
		$slide.find('.js-overlay').removeClass('is-visible');

		$infobox.find('.js-infobox-close').off(ns);

		var $video = $infobox.find('.js-infobox__video');

		if($video.length > 0) {
			// stop it
			$video[0].pause();

			var $playButton = $infobox.find('.js-infobox__video__play');
			if($playButton.length > 0) {
				$playButton.removeClass('is-hidden');
				$playButton.off(ns);
			}

			//iPad start-button workaround (otherwise it somehow won't start if loaded through world). Video has to be self toggled per controls
			if(IS_IOS) {
				//iphone workaround
				var $videoClone = $video.clone(),
					$videoContainer = $video.parent();
				$video.remove();
				$videoContainer.prepend($videoClone);

				$videoClone.attr('controls', true);
			}
		}


		if($infobox.find(".js-infobox__youtube")){
			var iFrameEle = $infobox.find(".js-infobox__youtube");
			this.resetYoutubeVideo(iFrameEle);
		}
	};


	Slideshow.prototype.resetYoutubeVideo = function(iFrameEle){
		var url = iFrameEle.attr('src');
		iFrameEle.attr('src', '');
		iFrameEle.attr('src', url);
	};
	
	Slideshow.prototype.resizeCoverBackground = function($slide) {
		var self = this;
		var $img = $slide.find('.js-slideshow-cover-bg');

		var imageWidth = $img.data('source-width') || 1920,
			imageHeight = $img.data('source-height') || 1080;

		var maxWidth = $img.data('max-width') || Number.MAX_VALUE,
		    maxHeight = $img.data('max-height') || Number.MAX_VALUE;

		var $offsetParent = $slide.offsetParent();
		var parentWidth = $offsetParent.width();
		var parentHeight = $offsetParent.height();

		var scaleMethod = $img.data('scale') || 'cover';

		// hack: to avoid markup changes:
		if ( $slide.is('.hotspot-container--products') ) {
			scaleMethod = 'contain';
			maxWidth = 1200;
		}
		// end of hack

		var minmax = scaleMethod == 'contain' ? Math.min : Math.max;

		var scale = minmax( Math.min(maxWidth, parentWidth) / imageWidth, Math.min(maxHeight, parentHeight) / imageHeight );
		imageWidth *= scale;
		imageHeight *= scale;

		$slide.css({
			'height' : imageHeight,
			'width' : imageWidth,
			'left' : (parentWidth - imageWidth) / 2,
			'top' : (parentHeight - imageHeight) / 2
		});

		$img.css({
			'height' : '100%',
			'width' : '100%'
		});
	};

	Slideshow.prototype.resizeAllBackgrounds = function() {
		var self = this;
		// hack: also selecting ".hotspot-container--products" to avoid markup changes:
		for (var i = self.$backgroundImages.length - 1; i >= 0; i--) {
			var $this = self.$backgroundImages.eq(i);

			self.resizeCoverBackground($this);
		}
	};

	Slideshow.prototype.initRouteNetworkLinks = function() {
	};

	Slideshow.prototype.initializeVideoSlides = function(){
		var self = this;

		self.$el.on("click"+ns, ".js-video-hotspot", function(){
			var $slideshowSlide = $(this).closest(".js-slideshow-slide");
			if($slideshowSlide.hasClass("is-initiated")){
				for(var i=0; i < self.videos.length; i++){
					if(self.videos[i]['index'] == $slideshowSlide.index()){
						self.videos[i]['instance'].playFromHotspot();
						break; 
					}
				}
				return;
			}
			
			var filmSlide = new FilmSlide($slideshowSlide);
			self.childModules.push( filmSlide );
			self.videos.push({index: $slideshowSlide.index(), instance:filmSlide});
		});

		this.$slides.filter('.has-video').each(function(index, el){
			var filmSlide = new FilmSlide(el);
			this.childModules.push( filmSlide );
			this.videos.push({index: $(el).index(), instance: filmSlide});
		}.bind(this));
	};

	Slideshow.prototype.pauseVideoSlideChanging = function() {
		for (var i = this.childModules.length - 1; i >= 0; i--) {
			if ( this.childModules[i].pauseFromSlideChanging ) {
				this.childModules[i].pauseFromSlideChanging();
			}
		}
	};

	Slideshow.prototype._debounce = function(func, wait, immediate) {
		var self = this;
		var timeout;

		return function() {
			var obj = this,
				args = arguments;

			if(timeout) {
				clearTimeout(timeout);
			}

			timeout = setTimeout(function() {
				func.apply(obj, args);
				timeout = null;
			}, wait || 100);
			if(immediate) {
				func.apply(obj, args);
			}
		};
	};

	return Slideshow;
});

/**
 * @preserve FastClick: polyfill to remove click delays on browsers with touch UIs.
 *
 * @version 0.6.11
 * @codingstandard ftlabs-jsv2
 * @copyright The Financial Times Limited [All Rights Reserved]
 * @license MIT License (see LICENSE.txt)
 */

/*jslint browser:true, node:true*/
/*global define, Event, Node*/


/**
 * Instantiate fast-clicking listeners on the specificed layer.
 *
 * @constructor
 * @param {Element} layer The layer to listen on
 */

function FastClick(layer) {
	'use strict';
	var oldOnClick, self = this;


	/**
	 * Whether a click is currently being tracked.
	 *
	 * @type boolean
	 */
	this.trackingClick = false;


	/**
	 * Timestamp for when when click tracking started.
	 *
	 * @type number
	 */
	this.trackingClickStart = 0;


	/**
	 * The element being tracked for a click.
	 *
	 * @type EventTarget
	 */
	this.targetElement = null;


	/**
	 * X-coordinate of touch start event.
	 *
	 * @type number
	 */
	this.touchStartX = 0;


	/**
	 * Y-coordinate of touch start event.
	 *
	 * @type number
	 */
	this.touchStartY = 0;


	/**
	 * ID of the last touch, retrieved from Touch.identifier.
	 *
	 * @type number
	 */
	this.lastTouchIdentifier = 0;


	/**
	 * Touchmove boundary, beyond which a click will be cancelled.
	 *
	 * @type number
	 */
	this.touchBoundary = 10;


	/**
	 * The FastClick layer.
	 *
	 * @type Element
	 */
	this.layer = layer;

	if (!layer || !layer.nodeType) {
		throw new TypeError('Layer must be a document node');
	}

	/** @type function() */
	this.onClick = function() { return FastClick.prototype.onClick.apply(self, arguments); };

	/** @type function() */
	this.onMouse = function() { return FastClick.prototype.onMouse.apply(self, arguments); };

	/** @type function() */
	this.onTouchStart = function() { return FastClick.prototype.onTouchStart.apply(self, arguments); };

	/** @type function() */
	this.onTouchMove = function() { return FastClick.prototype.onTouchMove.apply(self, arguments); };

	/** @type function() */
	this.onTouchEnd = function() { return FastClick.prototype.onTouchEnd.apply(self, arguments); };

	/** @type function() */
	this.onTouchCancel = function() { return FastClick.prototype.onTouchCancel.apply(self, arguments); };

	if (FastClick.notNeeded(layer)) {
		return;
	}

	// Set up event handlers as required
	if (this.deviceIsAndroid) {
		layer.addEventListener('mouseover', this.onMouse, true);
		layer.addEventListener('mousedown', this.onMouse, true);
		layer.addEventListener('mouseup', this.onMouse, true);
	}

	layer.addEventListener('click', this.onClick, true);
	layer.addEventListener('touchstart', this.onTouchStart, false);
	layer.addEventListener('touchmove', this.onTouchMove, false);
	layer.addEventListener('touchend', this.onTouchEnd, false);
	layer.addEventListener('touchcancel', this.onTouchCancel, false);

	// Hack is required for browsers that don't support Event#stopImmediatePropagation (e.g. Android 2)
	// which is how FastClick normally stops click events bubbling to callbacks registered on the FastClick
	// layer when they are cancelled.
	if (!Event.prototype.stopImmediatePropagation) {
		layer.removeEventListener = function(type, callback, capture) {
			var rmv = Node.prototype.removeEventListener;
			if (type === 'click') {
				rmv.call(layer, type, callback.hijacked || callback, capture);
			} else {
				rmv.call(layer, type, callback, capture);
			}
		};

		layer.addEventListener = function(type, callback, capture) {
			var adv = Node.prototype.addEventListener;
			if (type === 'click') {
				adv.call(layer, type, callback.hijacked || (callback.hijacked = function(event) {
					if (!event.propagationStopped) {
						callback(event);
					}
				}), capture);
			} else {
				adv.call(layer, type, callback, capture);
			}
		};
	}

	// If a handler is already declared in the element's onclick attribute, it will be fired before
	// FastClick's onClick handler. Fix this by pulling out the user-defined handler function and
	// adding it as listener.
	if (typeof layer.onclick === 'function') {

		// Android browser on at least 3.2 requires a new reference to the function in layer.onclick
		// - the old one won't work if passed to addEventListener directly.
		oldOnClick = layer.onclick;
		layer.addEventListener('click', function(event) {
			oldOnClick(event);
		}, false);
		layer.onclick = null;
	}
}


/**
 * Android requires exceptions.
 *
 * @type boolean
 */
FastClick.prototype.deviceIsAndroid = navigator.userAgent.indexOf('Android') > 0;


/**
 * iOS requires exceptions.
 *
 * @type boolean
 */
FastClick.prototype.deviceIsIOS = /iP(ad|hone|od)/.test(navigator.userAgent);


/**
 * iOS 4 requires an exception for select elements.
 *
 * @type boolean
 */
FastClick.prototype.deviceIsIOS4 = FastClick.prototype.deviceIsIOS && (/OS 4_\d(_\d)?/).test(navigator.userAgent);


/**
 * iOS 6.0(+?) requires the target element to be manually derived
 *
 * @type boolean
 */
FastClick.prototype.deviceIsIOSWithBadTarget = FastClick.prototype.deviceIsIOS && (/OS ([6-9]|\d{2})_\d/).test(navigator.userAgent);


/**
 * Determine whether a given element requires a native click.
 *
 * @param {EventTarget|Element} target Target DOM element
 * @returns {boolean} Returns true if the element needs a native click
 */
FastClick.prototype.needsClick = function(target) {
	'use strict';
	switch (target.nodeName.toLowerCase()) {

	// Don't send a synthetic click to disabled inputs (issue #62)
	case 'button':
	case 'select':
	case 'textarea':
		if (target.disabled) {
			return true;
		}

		break;
	case 'input':

		// File inputs need real clicks on iOS 6 due to a browser bug (issue #68)
		if ((this.deviceIsIOS && target.type === 'file') || target.disabled) {
			return true;
		}

		break;
	case 'label':
	case 'video':
		return true;
	}

	return (/\bneedsclick\b/).test(target.className);
};


/**
 * Determine whether a given element requires a call to focus to simulate click into element.
 *
 * @param {EventTarget|Element} target Target DOM element
 * @returns {boolean} Returns true if the element requires a call to focus to simulate native click.
 */
FastClick.prototype.needsFocus = function(target) {
	'use strict';
	switch (target.nodeName.toLowerCase()) {
	case 'textarea':
		return true;
	case 'select':
		return !this.deviceIsAndroid;
	case 'input':
		switch (target.type) {
		case 'button':
		case 'checkbox':
		case 'file':
		case 'image':
		case 'radio':
		case 'submit':
			return false;
		}

		// No point in attempting to focus disabled inputs
		return !target.disabled && !target.readOnly;
	default:
		return (/\bneedsfocus\b/).test(target.className);
	}
};


/**
 * Send a click event to the specified element.
 *
 * @param {EventTarget|Element} targetElement
 * @param {Event} event
 */
FastClick.prototype.sendClick = function(targetElement, event) {
	'use strict';
	var clickEvent, touch;

	// On some Android devices activeElement needs to be blurred otherwise the synthetic click will have no effect (#24)
	if (document.activeElement && document.activeElement !== targetElement) {
		document.activeElement.blur();
	}

	touch = event.changedTouches[0];

	// Synthesise a click event, with an extra attribute so it can be tracked
	clickEvent = document.createEvent('MouseEvents');
	clickEvent.initMouseEvent(this.determineEventType(targetElement), true, true, window, 1, touch.screenX, touch.screenY, touch.clientX, touch.clientY, false, false, false, false, 0, null);
	clickEvent.forwardedTouchEvent = true;
	targetElement.dispatchEvent(clickEvent);
};

FastClick.prototype.determineEventType = function(targetElement) {
	'use strict';

	//Issue #159: Android Chrome Select Box does not open with a synthetic click event
	if (this.deviceIsAndroid && targetElement.tagName.toLowerCase() === 'select') {
		return 'mousedown';
	}

	return 'click';
};


/**
 * @param {EventTarget|Element} targetElement
 */
FastClick.prototype.focus = function(targetElement) {
	'use strict';
	var length;

	// Issue #160: on iOS 7, some input elements (e.g. date datetime) throw a vague TypeError on setSelectionRange. These elements don't have an integer value for the selectionStart and selectionEnd properties, but unfortunately that can't be used for detection because accessing the properties also throws a TypeError. Just check the type instead. Filed as Apple bug #15122724.
	if (this.deviceIsIOS && targetElement.setSelectionRange && targetElement.type.indexOf('date') !== 0 && targetElement.type !== 'time') {
		length = targetElement.value.length;
		targetElement.setSelectionRange(length, length);
	} else {
		targetElement.focus();
	}
};


/**
 * Check whether the given target element is a child of a scrollable layer and if so, set a flag on it.
 *
 * @param {EventTarget|Element} targetElement
 */
FastClick.prototype.updateScrollParent = function(targetElement) {
	'use strict';
	var scrollParent, parentElement;

	scrollParent = targetElement.fastClickScrollParent;

	// Attempt to discover whether the target element is contained within a scrollable layer. Re-check if the
	// target element was moved to another parent.
	if (!scrollParent || !scrollParent.contains(targetElement)) {
		parentElement = targetElement;
		do {
			if (parentElement.scrollHeight > parentElement.offsetHeight) {
				scrollParent = parentElement;
				targetElement.fastClickScrollParent = parentElement;
				break;
			}

			parentElement = parentElement.parentElement;
		} while (parentElement);
	}

	// Always update the scroll top tracker if possible.
	if (scrollParent) {
		scrollParent.fastClickLastScrollTop = scrollParent.scrollTop;
	}
};


/**
 * @param {EventTarget} targetElement
 * @returns {Element|EventTarget}
 */
FastClick.prototype.getTargetElementFromEventTarget = function(eventTarget) {
	'use strict';

	// On some older browsers (notably Safari on iOS 4.1 - see issue #56) the event target may be a text node.
	if (eventTarget.nodeType === Node.TEXT_NODE) {
		return eventTarget.parentNode;
	}

	return eventTarget;
};


/**
 * On touch start, record the position and scroll offset.
 *
 * @param {Event} event
 * @returns {boolean}
 */
FastClick.prototype.onTouchStart = function(event) {
	'use strict';
	var targetElement, touch, selection;

	// Ignore multiple touches, otherwise pinch-to-zoom is prevented if both fingers are on the FastClick element (issue #111).
	if (event.targetTouches.length > 1) {
		return true;
	}

	targetElement = this.getTargetElementFromEventTarget(event.target);
	touch = event.targetTouches[0];

	if (this.deviceIsIOS) {

		// Only trusted events will deselect text on iOS (issue #49)
		selection = window.getSelection();
		if (selection.rangeCount && !selection.isCollapsed) {
			return true;
		}

		if (!this.deviceIsIOS4) {

			// Weird things happen on iOS when an alert or confirm dialog is opened from a click event callback (issue #23):
			// when the user next taps anywhere else on the page, new touchstart and touchend events are dispatched
			// with the same identifier as the touch event that previously triggered the click that triggered the alert.
			// Sadly, there is an issue on iOS 4 that causes some normal touch events to have the same identifier as an
			// immediately preceeding touch event (issue #52), so this fix is unavailable on that platform.
			if (touch.identifier === this.lastTouchIdentifier) {
				event.preventDefault();
				return false;
			}

			this.lastTouchIdentifier = touch.identifier;

			// If the target element is a child of a scrollable layer (using -webkit-overflow-scrolling: touch) and:
			// 1) the user does a fling scroll on the scrollable layer
			// 2) the user stops the fling scroll with another tap
			// then the event.target of the last 'touchend' event will be the element that was under the user's finger
			// when the fling scroll was started, causing FastClick to send a click event to that layer - unless a check
			// is made to ensure that a parent layer was not scrolled before sending a synthetic click (issue #42).
			this.updateScrollParent(targetElement);
		}
	}

	this.trackingClick = true;
	this.trackingClickStart = event.timeStamp;
	this.targetElement = targetElement;

	this.touchStartX = touch.pageX;
	this.touchStartY = touch.pageY;

	// Prevent phantom clicks on fast double-tap (issue #36)
	if ((event.timeStamp - this.lastClickTime) < 200) {
		event.preventDefault();
	}

	return true;
};


/**
 * Based on a touchmove event object, check whether the touch has moved past a boundary since it started.
 *
 * @param {Event} event
 * @returns {boolean}
 */
FastClick.prototype.touchHasMoved = function(event) {
	'use strict';
	var touch = event.changedTouches[0], boundary = this.touchBoundary;

	if (Math.abs(touch.pageX - this.touchStartX) > boundary || Math.abs(touch.pageY - this.touchStartY) > boundary) {
		return true;
	}

	return false;
};


/**
 * Update the last position.
 *
 * @param {Event} event
 * @returns {boolean}
 */
FastClick.prototype.onTouchMove = function(event) {
	'use strict';
	if (!this.trackingClick) {
		return true;
	}

	// If the touch has moved, cancel the click tracking
	if (this.targetElement !== this.getTargetElementFromEventTarget(event.target) || this.touchHasMoved(event)) {
		this.trackingClick = false;
		this.targetElement = null;
	}

	return true;
};


/**
 * Attempt to find the labelled control for the given label element.
 *
 * @param {EventTarget|HTMLLabelElement} labelElement
 * @returns {Element|null}
 */
FastClick.prototype.findControl = function(labelElement) {
	'use strict';

	// Fast path for newer browsers supporting the HTML5 control attribute
	if (labelElement.control !== undefined) {
		return labelElement.control;
	}

	// All browsers under test that support touch events also support the HTML5 htmlFor attribute
	if (labelElement.htmlFor) {
		return document.getElementById(labelElement.htmlFor);
	}

	// If no for attribute exists, attempt to retrieve the first labellable descendant element
	// the list of which is defined here: http://www.w3.org/TR/html5/forms.html#category-label
	return labelElement.querySelector('button, input:not([type=hidden]), keygen, meter, output, progress, select, textarea');
};


/**
 * On touch end, determine whether to send a click event at once.
 *
 * @param {Event} event
 * @returns {boolean}
 */
FastClick.prototype.onTouchEnd = function(event) {
	'use strict';
	var forElement, trackingClickStart, targetTagName, scrollParent, touch, targetElement = this.targetElement;

	if (!this.trackingClick) {
		return true;
	}

	// Prevent phantom clicks on fast double-tap (issue #36)
	if ((event.timeStamp - this.lastClickTime) < 200) {
		this.cancelNextClick = true;
		return true;
	}

	// Reset to prevent wrong click cancel on input (issue #156).
	this.cancelNextClick = false;

	this.lastClickTime = event.timeStamp;

	trackingClickStart = this.trackingClickStart;
	this.trackingClick = false;
	this.trackingClickStart = 0;

	// On some iOS devices, the targetElement supplied with the event is invalid if the layer
	// is performing a transition or scroll, and has to be re-detected manually. Note that
	// for this to function correctly, it must be called *after* the event target is checked!
	// See issue #57; also filed as rdar://13048589 .
	if (this.deviceIsIOSWithBadTarget) {
		touch = event.changedTouches[0];

		// In certain cases arguments of elementFromPoint can be negative, so prevent setting targetElement to null
		targetElement = document.elementFromPoint(touch.pageX - window.pageXOffset, touch.pageY - window.pageYOffset) || targetElement;
		targetElement.fastClickScrollParent = this.targetElement.fastClickScrollParent;
	}

	targetTagName = targetElement.tagName.toLowerCase();
	if (targetTagName === 'label') {
		forElement = this.findControl(targetElement);
		if (forElement) {
			this.focus(targetElement);
			if (this.deviceIsAndroid) {
				return false;
			}

			targetElement = forElement;
		}
	} else if (this.needsFocus(targetElement)) {

		// Case 1: If the touch started a while ago (best guess is 100ms based on tests for issue #36) then focus will be triggered anyway. Return early and unset the target element reference so that the subsequent click will be allowed through.
		// Case 2: Without this exception for input elements tapped when the document is contained in an iframe, then any inputted text won't be visible even though the value attribute is updated as the user types (issue #37).
		if ((event.timeStamp - trackingClickStart) > 100 || (this.deviceIsIOS && window.top !== window && targetTagName === 'input')) {
			this.targetElement = null;
			return false;
		}

		this.focus(targetElement);

		// Select elements need the event to go through on iOS 4, otherwise the selector menu won't open.
		if (!this.deviceIsIOS4 || targetTagName !== 'select') {
			this.targetElement = null;
			event.preventDefault();
		}

		return false;
	}

	if (this.deviceIsIOS && !this.deviceIsIOS4) {

		// Don't send a synthetic click event if the target element is contained within a parent layer that was scrolled
		// and this tap is being used to stop the scrolling (usually initiated by a fling - issue #42).
		scrollParent = targetElement.fastClickScrollParent;
		if (scrollParent && scrollParent.fastClickLastScrollTop !== scrollParent.scrollTop) {
			return true;
		}
	}

	// Prevent the actual click from going though - unless the target node is marked as requiring
	// real clicks or if it is in the whitelist in which case only non-programmatic clicks are permitted.
	if (!this.needsClick(targetElement)) {
		event.preventDefault();
		this.sendClick(targetElement, event);
	}

	return false;
};


/**
 * On touch cancel, stop tracking the click.
 *
 * @returns {void}
 */
FastClick.prototype.onTouchCancel = function() {
	'use strict';
	this.trackingClick = false;
	this.targetElement = null;
};


/**
 * Determine mouse events which should be permitted.
 *
 * @param {Event} event
 * @returns {boolean}
 */
FastClick.prototype.onMouse = function(event) {
	'use strict';

	// If a target element was never set (because a touch event was never fired) allow the event
	if (!this.targetElement) {
		return true;
	}

	if (event.forwardedTouchEvent) {
		return true;
	}

	// Programmatically generated events targeting a specific element should be permitted
	if (!event.cancelable) {
		return true;
	}

	// Derive and check the target element to see whether the mouse event needs to be permitted;
	// unless explicitly enabled, prevent non-touch click events from triggering actions,
	// to prevent ghost/doubleclicks.
	if (!this.needsClick(this.targetElement) || this.cancelNextClick) {

		// Prevent any user-added listeners declared on FastClick element from being fired.
		if (event.stopImmediatePropagation) {
			event.stopImmediatePropagation();
		} else {

			// Part of the hack for browsers that don't support Event#stopImmediatePropagation (e.g. Android 2)
			event.propagationStopped = true;
		}

		// Cancel the event
//		event.stopPropagation();
		event.preventDefault();

		return false;
	}

	// If the mouse event is permitted, return true for the action to go through.
	return true;
};


/**
 * On actual clicks, determine whether this is a touch-generated click, a click action occurring
 * naturally after a delay after a touch (which needs to be cancelled to avoid duplication), or
 * an actual click which should be permitted.
 *
 * @param {Event} event
 * @returns {boolean}
 */
FastClick.prototype.onClick = function(event) {
	'use strict';
	var permitted;

	// It's possible for another FastClick-like library delivered with third-party code to fire a click event before FastClick does (issue #44). In that case, set the click-tracking flag back to false and return early. This will cause onTouchEnd to return early.
	if (this.trackingClick) {
		this.targetElement = null;
		this.trackingClick = false;
		return true;
	}

	// Very odd behaviour on iOS (issue #18): if a submit element is present inside a form and the user hits enter in the iOS simulator or clicks the Go button on the pop-up OS keyboard the a kind of 'fake' click event will be triggered with the submit-type input element as the target.
	if (event.target.type === 'submit' && event.detail === 0) {
		return true;
	}

	permitted = this.onMouse(event);

	// Only unset targetElement if the click is not permitted. This will ensure that the check for !targetElement in onMouse fails and the browser's click doesn't go through.
	if (!permitted) {
		this.targetElement = null;
	}

	// If clicks are permitted, return true for the action to go through.
	return permitted;
};


/**
 * Remove all FastClick's event listeners.
 *
 * @returns {void}
 */
FastClick.prototype.destroy = function() {
	'use strict';
	var layer = this.layer;

	if (this.deviceIsAndroid) {
		layer.removeEventListener('mouseover', this.onMouse, true);
		layer.removeEventListener('mousedown', this.onMouse, true);
		layer.removeEventListener('mouseup', this.onMouse, true);
	}

	layer.removeEventListener('click', this.onClick, true);
	layer.removeEventListener('touchstart', this.onTouchStart, false);
	layer.removeEventListener('touchmove', this.onTouchMove, false);
	layer.removeEventListener('touchend', this.onTouchEnd, false);
	layer.removeEventListener('touchcancel', this.onTouchCancel, false);
};


/**
 * Check whether FastClick is needed.
 *
 * @param {Element} layer The layer to listen on
 */
FastClick.notNeeded = function(layer) {
	'use strict';
	var metaViewport;
	var chromeVersion;

	// Devices that don't support touch don't need FastClick
	if (typeof window.ontouchstart === 'undefined') {
		return true;
	}

	// Chrome version - zero for other browsers
	chromeVersion = +(/Chrome\/([0-9]+)/.exec(navigator.userAgent) || [,0])[1];

	if (chromeVersion) {

		if (FastClick.prototype.deviceIsAndroid) {
			metaViewport = document.querySelector('meta[name=viewport]');
			
			if (metaViewport) {
				// Chrome on Android with user-scalable="no" doesn't need FastClick (issue #89)
				if (metaViewport.content.indexOf('user-scalable=no') !== -1) {
					return true;
				}
				// Chrome 32 and above with width=device-width or less don't need FastClick
				if (chromeVersion > 31 && window.innerWidth <= window.screen.width) {
					return true;
				}
			}

		// Chrome desktop doesn't need FastClick (issue #15)
		} else {
			return true;
		}
	}

	// IE10 with -ms-touch-action: none, which disables double-tap-to-zoom (issue #97)
	if (layer.style.msTouchAction === 'none') {
		return true;
	}

	return false;
};


/**
 * Factory method for creating a FastClick object
 *
 * @param {Element} layer The layer to listen on
 */
FastClick.attach = function(layer) {
	'use strict';
	return new FastClick(layer);
};


if (typeof define !== 'undefined' && define.amd) {

	// AMD. Register as an anonymous module.
	define('vendor/fastclick',[],function() {
		'use strict';
		return FastClick;
	});
} else if (typeof module !== 'undefined' && module.exports) {
	module.exports = FastClick.attach;
	module.exports.FastClick = FastClick;
} else {
	window.FastClick = FastClick;
}
;

define('slideshow',['app/content/Slideshow', 'vendor/fastclick', 'mousewheel'], function(Slideshow, FastClick){

	var slideshow;
	function initPage() {
		if ( FastClick && FastClick.attach ) {
			FastClick.attach(document.body);
		}
		slideshow = new Slideshow();
	}
	function destroyPage(){
		slideshow.destroy();
	}

	var page = {};
	page.init = function(element) {
		this.element = $(element);
		initPage();
	};
	page.destroy = function() {
		destroyPage();
	};

	return page;
});

define (
'app/content/Film',[
	'jquery',
	'app/content/FilmHotspot',
	'hv/animation/AnimationFrame',
	'app/Config',
	'app/modules/GATracker'
],
function(
	$,
	FilmHotspot,
	AnimationFrame,
	Config,
	GATracker
) {
	var ns = '.film';
	var self;

	var $window,
		windowHeight,
		windowWidth;


	function Film() {
		self = this;
		self.$el = $('.js-video');
		self.$window = $(window);
		self.windowHeight = self.getWindowHeight();
		self.windowWidth = self.$window.width();
		self.loadedEventTriggered = false;
		self.hasRelatedMedia = self.$el.hasClass("has-related_media");

		self.$video = $('.js-video');
		self.video = $('.js-video')[0];
		self.$closeButton = $(".js-content-close");
		self.requestAnimationFrame = true;
		self.lastCurrPercentage = -1;

		this.trackingData = this.$video.data('tracking');

		self.checkDelayedAutoplay();

		if(this.trackingData.hotspots.length > 0) {
			self.$hotspot = $(this.trackingData.hotspots[0].id);
		}

		self.hotspots = [];
		self.videoWidth = self.$video.width();
		self.videoHeight = self.$video.height();
		self.waiting = 0;

		self.$playButton = $('.js-play-button');
		if(Modernizr.touch) {
			self.$playButton.on('click'+ns+' touchstart'+ns, self.playButtonClick);
			self.$video.one('play'+ns, self.playButtonClick);
		}

		//self.$loadingIndicator = $('.js-video-loading');

		self.resizeFilm();
		self.initHotspotTracking();

		self.$window.on('resize'+ns, self.onResize);

		self.$video.on('canplay'+ns, function(){
			self.resizeFilm();
		});

		// disable scrolling on touch devices
		$(document).on('touchstart'+ns, function(e){
			e.preventDefault();
		});

		self.$video.on('loadedmetadata'+ns, function(e) {
			self.resizeFilm();
		});

		self.initVideoControls();

		self.checkLoaded();

		$('.js-content-close').on('click'+ns, function(e) {
			$('.js-video-progress-control').css('display', 'none');
			$('.js-content-container').removeClass('is-animated');
			self.pauseVideo();

			$(this).trigger('wos-film-content-close-click');
		});

		$('body').on('shareboxOpen'+ns, function(e) {
			self.hasInfoboxOpened = true;
			self.pauseVideo();
		});
		$('body').on('shareboxClose'+ns, function(e) {
			self.hasInfoboxOpened = false;
			// don't autoplay on mobile
			if(self.windowWidth > 750) {
				setTimeout(function() {
					self.playVideo();
				}, 300);
			}
		});

		self.$video.on('ended'+ns, function(e) {
			// self.$closeButton.trigger('click');
		});

		self.$video.on('canplaythrough'+ns, function(e) {
			if(!self.hasInfoboxOpened) {
				self.playVideo();
			}
		});

		self.displayControls(false);

		if($('body').hasClass('content-film-body')) {
			$('.js-content-container').addClass('is-animated');
		}

		// hack for android
		if(self.android) {
			$('.js-play-button').addClass('video-play-button--visible');
			$('body').on('touchstart'+ns, '.js-content-close', function() {
				$(this).trigger('click');

				if($('body').hasClass('content-film-body')) {
					window.location = $(this).attr('href');
				}
			});
		}
		// hack for iphone
		if(self.iOS) {
			$('html').addClass('is-iOS');
		}

	}

	Film.prototype.android = (/android/i).test(navigator.userAgent);
	Film.prototype.iOS = /iP(ad|hone|od)/.test(navigator.userAgent);
	Film.prototype.iOS7 = (/iPad;.*CPU.*OS 7_\d/i).test(navigator.userAgent);

	Film.prototype.checkDelayedAutoplay = function() {
		$('body').on('showTransitionStart.roundMask'+ns, onTransitionStart);

		function onTransitionStart() {
			self.pauseVideo({
				'displayControls' : false
			});

			$('body').on('showTransitionEnd.roundMask'+ns, onTransitionEnd);
		}
		function onTransitionEnd() {
			self.playVideo({
				'delayed' : true
			});

			$('.js-content-container').addClass('is-animated');

			$('body').off('showTransitionStart.roundMask'+ns, onTransitionStart);
			$('body').off('showTransitionEnd.roundMask'+ns, onTransitionEnd);
		}
	};

	Film.prototype.checkLoaded = function() {
		if (self.video.readyState >= 3 ) {
			self.triggerLoadedEvent();
		} else {
			self.$video.on('loadeddata ' + ns + ' loadedmetadata'+ns + ' oncanplay'+ns + ' canplaythrough' + ns + ' loadstart' + ns + ' stalled' + ns, self.triggerLoadedEvent);
		}
		setTimeout(function(e) {
			self.triggerLoadedEvent();
		}, Modernizr.touch ? 0 : 500);
	};

	Film.prototype.triggerLoadedEvent = function() {
		if(!self.loadedEventTriggered) {
			self.loadedEventTriggered = true;
			self.$video.trigger('content.loaded');
			self.$video.off('loadeddata ' + ns + ' loadedmetadata'+ns + ' oncanplay'+ns + ' canplaythrough' + ns + ' loadstart' + ns + ' stalled' + ns, self.triggerLoadedEvent);
		}
	};

	Film.prototype.destroy = function() {
		// avoid video buffering.
		// this may cause player to emit errors but they are harmless
		self.video.src = '';
		self.$el.off(ns);
		$(document).off(ns);
		$(window).off(ns);
		self.$el = null;
		self = null;
	};

	Film.prototype.initVideoControls = function() {
		var $progressBar = $('.js-progress-bar');
		var $loadingBar = $('.js-loading-bar');
		var $progressControl = $('.js-video-progress-control');

		self.toggleControlsOnClick();
		if(Modernizr.touch) {
			self.updatePlayToggle(false);
		}

		self.$video.on('progress'+ns, function() {
			if(this.buffered.length >= 1) {
				var percentage = Math.ceil((this.buffered.end(0) / this.duration) * 100);
				if(percentage >= 100) {
					$loadingBar.css('display', 'none');
				} else {
					$loadingBar.css('width', percentage + '%');
				}
			}
		});

		self.$video.on('timeupdate'+ns, function(e) {
			var percentage = Math.floor((100 / self.video.duration) * self.video.currentTime);
			$progressBar.css('width', percentage + '%');

			if(self.android) {
				self.videoStartTime = new Date().getTime() - (self.video.currentTime * 1000);
			}

			if(self.hasRelatedMedia){
				if(self.video.currentTime >= self.video.duration - 7){
					$(".js-content-container").addClass('is-ending');
				}else{
					$(".js-content-container").removeClass('is-ending');
				}
			}

			self.sendTrackEvent();
		});

		// on first play (can't listen to 'play'-evt because it isn't fired when autoplay="autoplay" on the first time)
		self.$video.one('timeupdate'+ns, function(e) {
			// avoid repaints due to background on $video
			self.$video.css({
				'background' : 'none'
			});
			$('.js-video-poster').remove();
		});

		self.$video.on('pause'+ns, function(e) {
			self.pauseVideo({
				'displayControls' : false
			});
		});

		$progressControl.on('click'+ns, function(e) {
			e.preventDefault();

			var clickPos = e.pageX,
				totalWidth = $progressControl.outerWidth(),
				newPercentage = clickPos / totalWidth;

			self.hideAllHotspots();

			self.video.currentTime = newPercentage * self.video.duration;
			self.playVideo();

			self.$el.trigger('wos-film-progress-bar-click');
		});

		self.$video.on('waiting', function(e) {
			if(self.waiting > 0) {
				self.displayLoadingIndicator();
			}
			self.waiting += 1;
		});

		$('.js-video-play-toggle').on('click'+ns, function(e) {
			e.stopPropagation();
			e.preventDefault();

			var $this = $(this);

			if(self.isVideoStopped) {
				self.playVideo();
				$this.trigger('wos-film-play-click');
			} else {
				self.pauseVideo();
				$this.trigger('wos-film-pause-click');
			}

			$this.trigger('wos-film-play-toggle-click');
		});

		$('.js-video-mute-toggle').on('click'+ns, function(e) {
			e.stopPropagation();
			e.preventDefault();
			var $this = $(this);

			var isMuted = self.video.muted;

			if(isMuted) {
				$this.addClass('video-mute-toggle--mute').removeClass('video-mute-toggle--unmute');
				$('.video-mute-toggle__desc').text(Config.get('langVideoMute'));
				$this.trigger('wos-film-unmute-click');
			} else {
				$this.addClass('video-mute-toggle--unmute').removeClass('video-mute-toggle--mute');
				$('.video-mute-toggle__desc').text(Config.get('langVideoUnmute'));
				$this.trigger('wos-film-mute-click');
			}

			self.video.muted = !isMuted;

			$this.trigger('wos-film-mute-toggle-click');
		});

		$(window).on('keydown'+ns, function(e) {
			if(e.keyCode === 32) { // spacebar
				if(self.isVideoStopped) {
					self.playVideo();
				} else {
					self.pauseVideo();
				}
			}
		});
	};

	Film.prototype.sendTrackEvent = function() {
		var self = this;

		var href = window.location.pathname;
		var currentPercentage = Math.floor(self.video.currentTime * 100 / self.video.duration);
		var previousPercentage = this.previousPercentage || 0;
		if ((currentPercentage < previousPercentage) < 0 || (currentPercentage < previousPercentage) > 2) {
			// probably a manual time shift
			// we could ignore this here ...
		}
		currentPercentage = Math.floor(currentPercentage / 25) * 25; // round to 0, 25, 50, 75, 100
		if (self.lastCurrPercentage !== currentPercentage) {
			GATracker.track('send', 'event', 'video', 'play', href, currentPercentage);
			self.lastCurrPercentage = currentPercentage;
		}

	};

	Film.prototype.displayLoadingIndicator = function() {
		$('.js-video-play-toggle').addClass('video-play-toggle--loading');
		self.displayControls(true);
	};

	Film.prototype.updatePlayToggle = function(isPlaying) {
		isPlaying = isPlaying || !self.isVideoStopped;
		var $controls = $('.js-video-progress-control');

		if(isPlaying) {
			$('.js-video-play-toggle-text').text(Config.get('langVideoPause'));
			$('.js-video-play-toggle').addClass('video-play-toggle--pause').removeClass('video-play-toggle--play');
		} else {
			//pause
			$('.js-video-play-toggle-text').text(Config.get('langVideoPlay'));
			$('.js-video-play-toggle').addClass('video-play-toggle--play').removeClass('video-play-toggle--pause');
		}
	};

	Film.prototype.displayControls = function(visible) {
		var $controls = $('.js-video-progress-control');

		if(visible) {
			$controls.addClass('hovered');

			// hide it after n seconds
			clearTimeout(self.controlsTimeout);
			self.controlsTimeout = setTimeout(function() {
				if(self && !self.isVideoStopped) {
					self.displayControls(false);
				}
			}, 3000);
		} else {
			clearTimeout(self.controlsTimeout);
			$controls.removeClass('hovered');
		}
	};

	Film.prototype.toggleControlsOnClick = function() {
		var isVisible = true;

		self.$video.on('click'+ns+' touchstart'+ns, function(e) {
			isVisible = !isVisible;
			self.displayControls(isVisible);
		});

		return false;
	};

	Film.prototype.initHotspotTracking = function() {
		$('.js-hotspot').each(function() {
			var $this = $(this);

			self.hotspots.push(new FilmHotspot($this));
		});

		$('.js-hotspot:not(is-hidden)').on('mouseenter'+ns + ' touchstart'+ns, function() {
			if(!self.hasInfoboxOpened) {
				clearTimeout(self.timeout);
				self.isHotspotHovered = true;
				self.pauseVideo({
					'displayControls' : false
				});
			}
		});
		$('.js-hotspot:not(is-hidden)').on('mouseleave'+ns + ' touchstart'+ns, function() {
			if(!self.hasInfoboxOpened) {
				self.isHotspotHovered = false;
				self.playVideo({
					'delayed' : true
				});
			}
		});


		$(document).on('infoboxOpened'+ns, function() {
			self.pauseVideo({
				'displayControls' : false
			});
			clearTimeout(self.timeout);
			self.hasInfoboxOpened = true;
			self.isHotspotHovered = true;
		});
		$(document).on('infoboxClosed'+ns, function() {
			self.hasInfoboxOpened = false;
			self.isHotspotHovered = false;

			self.playVideo({
				'delayed' : true
			});
		});

		AnimationFrame.request(self.moveHotspots);
	};

	Film.prototype.moveHotspots = function(timestamp) {
		if(self === null) return;

		var currentFrame = Math.round(self.video.currentTime * self.trackingData.fps);

		if(self.android && !self.isVideoStopped) {
			if(self.video.currentTime > 0) {
				var playedTime = (new Date().getTime() - self.videoStartTime) / 1000;
				currentFrame = Math.round(playedTime * self.trackingData.fps);
			}
		}

		// only once per frame
		if(currentFrame !== self.lastFrame) {
			// console.log('droppedFrames: ' + self.video.webkitDroppedFrameCount);

			if(!self.activeHotspot) {
				self.activeHotspot = self.findHotspot(currentFrame);

				if(self.activeHotspot) {
					self.$hotspot = $(self.activeHotspot.id);
					self.halfHotspotWidth = self.$hotspot.outerWidth() / 2;
				}
			}

			var hotspot = self.activeHotspot;

			if(hotspot) {
				var hotspotCords = hotspot.frames[(currentFrame - hotspot.startFrame - 1)]; //anpassung frame

				if(hotspotCords) {
					self.setHotspotPosition(self.$hotspot, (hotspotCords.x * self.factorX - self.halfHotspotWidth), (hotspotCords.y * self.factorY - self.halfHotspotWidth));

					//check for fade out
					if(currentFrame >= (hotspot.startFrame + hotspot.frames.length - 10)) { // -5 -> fade out 5 frames früher
						self.$hotspot.addClass('is-hidden').removeClass('hotspot--tooltip-visible');
					}
				} else {
					self.activeHotspot = undefined;
				}

				self.lastFrame = self.currentFrame;
			}
		}

		self.animationFrame = AnimationFrame.request(self.moveHotspots);
	};

	Film.prototype.setHotspotPosition = function($hotspot, x, y) {
		if(Modernizr.csstransforms3d) {
			self.$hotspot.css({
				'-webkit-transform': 'translate3d(' + x + 'px,' + y + 'px, 0)',
				'-moz-transform': 'translate3d(' + x + 'px,' + y + 'px, 0)',
				'transform': 'translate3d(' + x + 'px,' + y + 'px, 0)'
			}).removeClass('is-hidden').addClass('hotspot--tooltip-visible');
		} else if(Modernizr.csstransforms) {
			self.$hotspot.css({
				'transform': 'translate(' + x + 'px,' + y + 'px)'
			}).removeClass('is-hidden').addClass('hotspot--tooltip-visible');
		} else {
			self.$hotspot.css({
				'top' : y,
				'left' : x
			}).removeClass('is-hidden').addClass('hotspot--tooltip-visible');
		}
	};

	Film.prototype.hideAllHotspots = function() {
		$('.js-hotspot').removeClass('hotspot--tooltip-visible').addClass('is-hidden');
	};

	Film.prototype.findHotspot = function(currentFrame) {
		var hotspots = this.trackingData.hotspots;

		for (var i = hotspots.length - 1; i >= 0; i--) {
			var hotspot = hotspots[i];

			if(hotspot.startFrame + 2 == currentFrame) { // delayed fade in -> hotspot.startFrame + 5
				return hotspot;
			} else if(hotspot.startFrame + 2 <= currentFrame && (hotspot.startFrame + hotspot.frames.length) > currentFrame) { // delayed fade in -> hotspot.startFrame + 5
				return hotspot;
			}
		}
	};

	Film.prototype.playVideo = function(options) {
		if(self.hasInfoboxOpened) {
			$('.js-overlay').trigger('click');
		}

		$('.js-video-play-toggle').removeClass('video-play-toggle--loading');

		if(options) {
			if(options.delayed) {
				return setTimeout(function() {
					startVideo(options);
				}, 500);
			}
		} else {
			startVideo(options);
		}

		function startVideo(options) {
			self.isVideoStopped = false;
			self.updatePlayToggle(true);
			self.video.play();
			if(self.android) {
				self.$video.one('timeupdate'+ns, function(e) {
					self.videoStartTime = new Date().getTime() - (self.video.currentTime * 1000);
					self.animationFrame = AnimationFrame.request(self.moveHotspots);
				});
			} else {
				self.animationFrame = AnimationFrame.request(self.moveHotspots);
			}
			//self.$playButton.css({display: 'none'});
		}
	};

	Film.prototype.pauseVideo = function(options) {
		self.isVideoStopped = true;
		self.updatePlayToggle(false);
		self.video.pause();
		AnimationFrame.cancel(self.animationFrame);

		if(options) {
			if(options.displayControls && options.displayControls === true) {
				self.displayControls(true);
			}
		} else {
			if(!self.hasInfoboxOpened && !self.isHotspotHovered) {
				self.displayControls(self.isVideoStopped);
			}
		}
		//self.$playButton.css({display: ''});
	};

	Film.prototype.onResize = function(e) {
		self.windowWidth = self.$window.width();
		self.windowHeight = self.getWindowHeight();

		self.resizeFilm();
	};

	Film.prototype.playButtonClick = function() {
		self.$video.off('play'+ns, self.playButtonClick);

		$('.js-video-poster').remove();
		self.playVideo();
		self.$playButton.css({
			'display':'none'
		});
	};

	Film.prototype.resizeFilm = function() {
		self.windowHeight = self.getWindowHeight(); //because of ios7 bug
		self.windowWidth = self.$window.width();

		//on other browsers it is solved over css
		//if(self.iOS) {
			// strangely if width/height is read over $video.height() it returns the wrong value...
			var newDimensions = self.scaleFilm();

			self.videoHeight = newDimensions.height;
			self.videoWidth = newDimensions.width;
		/*} else {
			self.videoHeight = self.$video.height();
			self.videoWidth = self.$video.width();
		}*/

		var $videoWrapper = $('.js-video-wrapper');

		//if(newDimensions.scale === 'stretch') {

			//CHECK THIS AGAIN
			var marginLeft = Math.round(((self.videoWidth - self.windowWidth) / 2) * -1);
			var marginTop = Math.round(((self.videoHeight - self.windowHeight) / 2) * -1);

			$videoWrapper.css({
				'left': marginLeft,
				'top': marginTop
			});
		/*} else {
			$videoWrapper.css({
				'left': 0,
				'top': 0
			});

		}*/

		self.factorY = self.videoHeight / this.trackingData.sourceHeight;
		self.factorX = self.videoWidth / this.trackingData.sourceWidth;

		self.setHotspotStartPositions();
	};

	Film.prototype.setHotspotStartPositions = function() {
		var i;

		for (i = this.trackingData.hotspots.length - 1; i >= 0; i--) {
			var hotspot = this.trackingData.hotspots[i],
				$hotspot = $(hotspot.id),
				hotspotCords = hotspot.frames[0];

			$hotspot.css({
				'-webkit-transform': 'translate3d(' + (hotspotCords.x * self.factorX - 20) + 'px,' + (hotspotCords.y * self.factorY - 20) + 'px, 0)',
				'-moz-transform': 'translate3d(' + (hotspotCords.x * self.factorX - 20) + 'px,' + (hotspotCords.y * self.factorY - 20) + 'px, 0)',
				'transform': 'translate3d(' + (hotspotCords.x * self.factorX - 20) + 'px,' + (hotspotCords.y * self.factorY - 20) + 'px, 0)'
			});
		}
	};

	Film.prototype.scaleFilm = function() {
		var aspectRatio = this.trackingData.sourceWidth / this.trackingData.sourceHeight,
			windowRation = self.windowWidth / self.windowHeight;

		var dimensions = {
			'height' : '',
			'width' : '',
			'scale' : 'none'
		};

		if(aspectRatio > windowRation) {
			dimensions.scale = 'stretch'
			dimensions.height = self.windowHeight;
			dimensions.width = Math.round(this.trackingData.sourceWidth * (self.windowHeight / this.trackingData.sourceHeight));
		} else if(aspectRatio < windowRation) {
			dimensions.scale = 'stretch'
			dimensions.height = Math.round(this.trackingData.sourceHeight * (self.windowWidth / this.trackingData.sourceWidth));
			dimensions.width = self.windowWidth;
		}

		self.$video.css(dimensions);

		return dimensions;
	};

	Film.prototype.getWindowHeight = function() {
		//ios7 landscape windowHeight bug.
		if (self.iOS7) {
			window.scrollTo(0, 0);
			return window.innerHeight;
		}

		return self.$window.height();
	};

	return Film;
});

define('film',['app/content/Film', 'vendor/fastclick', 'mousewheel'], function(Film, FastClick){

	var film;
	function initPage() {
		if ( FastClick && FastClick.attach ) {
			FastClick.attach(document.body);
		}
		film = new Film();
	}
	function destroyPage() {
		film.destroy();
	}

	var page = {};
	page.init = function(element) {
		this.element = $(element);
		initPage();
	};
	page.destroy = function() {
		destroyPage();
	};

	return page;
});

define (
'app/content/Foldshow',[
	'jquery',
	'app/content/BaseModule',
	'app/util/Utils', 
	'hv/animation/AnimationFrame',
	'app/modules/GATracker'
],
function(
	$, BaseModule, Utils, AnimationFrame, GATracker
) {
	var ns = '.Foldshow';
	var instance; /* singleton impl. */
	var instanceCounter = 0;

	var Foldshow = function() {
		this.ns = ns + instanceCounter++;
		this.init();
		this.childModules = [];
	};

	Foldshow.prototype = new BaseModule();

	Foldshow.prototype.init = function() {
		var self = this;

		this.$foldshow = $(".js-foldshow");
		this.$slide = $(".js-foldshow__slide");
		this.$step = $(".js-foldshow__step");
		this.$stepInner = $(".js-foldshow__step").find("> div");
		this.$stepContent = $(".js-foldshow__content");
		this.$backgroundImage = $(".js-background-image");
		this.$pagination = $(".js-foldshow-pagination");
		this.$paginationItem = null;

		this.currentStepIndex = 0;

		this.lastScroll = new Date().getTime();
		
		this.numberOfSlide = this.$slide.length;
		this.numberOfChild = this.$step.length;

		this.setBackgroundCover();
		this.setBackgroundColor();

		self.handleResize();
		self.setScene();

		if(window.location.hash && (window.location.hash).indexOf('slide=') != -1) {
			var hash = window.location.hash;
			var startIndex = parseInt(hash.split('slide=').pop(), 10);
			self.currentStepIndex = startIndex;

			setTimeout(function(e) { // b/c. of safari
				self.goToStep(startIndex);
			},0);
		} else {
			setTimeout(function(e) { // b/c. of safari
				self.goToStep(self.currentStepIndex);
			},0);
		}

	};

	Foldshow.prototype.setScene = function() {
		var self = this; 

		var winWidth = $(window).width();

		self.createPagination();

		if(Modernizr.touch  || winWidth < 1025) {
			$("html, body").css({
				"overflow": "auto",
				"height": "auto"
			});

			$(document).on('showTransitionEnd.roundMask', function() {
				$('#contentcontainerid, #contentinnercontid').css({
					'overflow': 'auto',
					'height': 'auto',
					'position': 'static'
				});
			});
			self.hidePagination();
		} else {
			self.handleMouseWheel();
			self.handleKeyboard();
			self.showPagination();
			self.$paginationItem.on("click", function(){
				self.goToStep($(this).index());
			});
		}
	};

	Foldshow.prototype.handleResize = function() {
		var self = this;

		$(window).on("resize", function() {

			var winWidth = $(window).width();

			self.currentStepIndex = self.currentStepIndex;

			if(Modernizr.touch || winWidth <= 1024) {
				$("html, body").css({
					"overflow": "auto",
					"height": "auto"
				});
				self.$step.css("z-index", "1");
				self.hidePagination();
				$(window).off("mousewheel"+ns);
				$(document).off("keyup"+ns);
			} else {
				$("html, body").css({
					"overflow": "none",
					"height": "100%"
				});
				self.showPagination();

				self.$step.css("z-index", "-999");
				self.$step.eq(self.currentStepIndex).find("> div").addClass("is-in");
				self.$step.eq(self.currentStepIndex).css("z-index", "1");

				self.handleMouseWheel();
				self.handleKeyboard();
			}
			
			self.setBackgroundCover();
		});
	};

	Foldshow.prototype.setBackgroundCover = function() {
		var self = this;

		this.$stepInner.each(function() {
			var $image = $(this).find(self.$backgroundImage);

			var originalImageWidth = $image.data('source-width') || 1920;
			var originalImageHeight = $image.data('source-height') || 1080;

			var $offsetParent = $image.offsetParent();
			var parentWidth = Math.round($offsetParent.width()) || $(window).width();
			var parentHeight = $offsetParent.height() || $(window).height();

			var s = scale = Math.max( parentHeight/originalImageHeight , parentWidth/originalImageWidth);

			var left = (parentWidth - originalImageWidth) / 2,
				top = (parentHeight - originalImageHeight) / 2;

			var css = {
				'position': 'absolute',
		  		'left': left,
		  		'top': top,
		  		'width': originalImageWidth,
		  		'transform': Modernizr.csstransforms3d ? 'scale3d('+[s,s,s].join(',')+')' : 'scale('+s+')'
		  	};

		  	$image.css(css);
		});
	};

	Foldshow.prototype.setBackgroundColor = function() {
		this.$stepContent.each(function(){
			var hisData = $(this).data("color");
			$(this).css({"background-color": hisData});
			$(this).find(".foldshow__content__link-wrap").css({"background-color": hisData});
		});
	};

	Foldshow.prototype.handleMouseWheel = function () {
		var self = this;
		$(window).on('mousewheel'+ns, mousewheelHandler);

		function mousewheelHandler(e, delta) {

			e.preventDefault();

			if(self.lastScroll + 1000 < new Date().getTime()) {
				if(e.originalEvent.wheelDelta > 50 || delta >= 1 || (/firefox/i.test(navigator.userAgent) && delta >= 1)) { //20
					//scrolling up
					self.lastScroll = new Date().getTime();
					self.getPrevStep();
				} else if(e.originalEvent.wheelDelta < -50 || delta <= -1 || (/firefox/i.test(navigator.userAgent) && delta <= -1)) { //20
					//scrolling down
					self.lastScroll = new Date().getTime();
					self.getNextStep();
				}
			}
		}
	};

	Foldshow.prototype.handleKeyboard = function() {
		var self = this; 

		$(document).on('keyup'+ns, function(e) {
			if(self.lastScroll + 600 < new Date().getTime()) {
				if (e.keyCode === 38) {
					self.getPrevStep();
					self.lastScroll = new Date().getTime();
				} else 
				if (e.keyCode === 40) {
					self.lastScroll = new Date().getTime();
					self.getNextStep();
				}
			}
		});
	};

	Foldshow.prototype.getPrevStep = function () {
		var self = this;
		if(self.currentStepIndex <= 0) {
			self.currentStepIndex = 0;
		} else {
			self.goToStep(this.currentStepIndex - 1);
		}
	};

	Foldshow.prototype.getNextStep = function() {
		var self = this;
		if(self.currentStepIndex >= self.numberOfChild - 1) {
			self.currentStepIndex = self.numberOfChild - 1;
		} else {
			self.goToStep(this.currentStepIndex + 1);
		}
	};

	// Pagination 

	Foldshow.prototype.createPagination = function() {
		var self = this; 

		for (var i = 0; i < self.numberOfChild; i++) {
			self.$pagination.append('<li class="foldshow_pagination--item""> '+ self.numberOfChild +'</li>');
		};

		this.$paginationItem = $(".foldshow_pagination--item");

		this.$pagination.append('<li class="active-pager-circle"></li>');
	};

	Foldshow.prototype.updatePagination = function() {
		var self = this; 
		var $activePager = this.$paginationItem.eq(self.currentStepIndex).addClass('is-active');
		var $activePagerCircle = $('.active-pager-circle');

		$activePagerCircle.css({
			'top': $activePager.position().top
		});
	};

	Foldshow.prototype.hidePagination = function() {
		this.$pagination.hide();
	};

	Foldshow.prototype.showPagination = function() {
		this.$pagination.show();
	};

	Foldshow.prototype.goToStep = function(nbreIndex) {
		var self = this; 

		var indexGoal = nbreIndex;

		var oldCurrentSlide = self.currentStepIndex;

		var incr = 0; 
		var numberOfHisChild = self.$step.eq(indexGoal).find("> div").length;

		if(indexGoal >= oldCurrentSlide) {
			// Go forward
			self.$step.eq(indexGoal).css("z-index", "1");

			var interval = setInterval(function() {
				if(incr <= numberOfHisChild) {
					self.$step.eq(indexGoal).find("> div").eq(incr).addClass("is-in");
					incr++;
				} else {
					window.clearInterval(interval);
				}
			}, 175);
		}
		
		if(indexGoal < oldCurrentSlide) {
			// Go back
			self.$step.eq(indexGoal).css("z-index", "1");
			self.$step.eq(indexGoal).find("> div").addClass("is-in");

			incr = self.$step.eq(oldCurrentSlide).find("> div").length;
			var intervalBack = setInterval(function() {
				if(incr < 0) {
					window.clearInterval(intervalBack);
				} else {
					self.$step.eq(oldCurrentSlide).find("> div").eq(incr).removeClass("is-in");
					incr--;
				}
			}, 100);
			self.currentStepIndex--;


			self.$step.css("z-index", "-999");
			self.$step.eq(oldCurrentSlide).css("z-index", "1");
			self.$step.eq(indexGoal).css("z-index", "1");

			setTimeout(function(){
				self.$step.eq(oldCurrentSlide).find("> div").removeClass("is-in");
				self.$step.eq(oldCurrentSlide).css("z-index", "-999");
			}, 800);
		}

		self.currentStepIndex = indexGoal;
		self.updatePagination();

		GATracker.replaceLocation('#slide=' + self.currentStepIndex, 'Slide');
	};


	return Foldshow;
});

define('foldshow',['app/content/Foldshow', 'vendor/fastclick', 'mousewheel'], function(Foldshow, FastClick){

	var foldshow;
	function initPage() {
		if ( FastClick && FastClick.attach ) {
			FastClick.attach(document.body);
		}
		foldshow = new Foldshow();
	}
	function destroyPage(){
		foldshow.destroy();
	}

	var page = {};
	page.init = function(element) {
		this.element = $(element);
		initPage();

		this.element.trigger('content.loaded');
	};
	page.destroy = function() {
		destroyPage();
	};

	return page;
});

define('hv/util/fps',[], function(){


	// Preferred timing funtion
	var w = window;
	var getTime, time, frameId;

	var fps, frameTime = 0;

	var SMOOTHING = 10;



	(function () {
		var perf = w.performance;
		if (perf && (perf.now || perf.webkitNow)) {
			var perfNow = perf.now ? 'now' : 'webkitNow';
			getTime = perf[perfNow].bind(perf);
		} else {
			getTime = function () {
				return +new Date();
			};
		}
	}());

	// Local WindowAnimationTiming interface polyfill
	var cAF = w.cancelAnimationFrame || w.cancelRequestAnimationFrame;
	var rAF = w.requestAnimationFrame;
	(function () {
		var vendors = ['moz', 'webkit', 'o'];
		var lastTime = 0;

		// For a more accurate WindowAnimationTiming interface implementation, ditch the native
		// requestAnimationFrame when cancelAnimationFrame is not present (older versions of Firefox)
		for (var i = 0, l = vendors.length; i < l && !cAF; ++i) {
			cAF = w[vendors[i]+'CancelAnimationFrame'] || w[vendors[i]+'CancelRequestAnimationFrame'];
			rAF = cAF && w[vendors[i]+'RequestAnimationFrame'];
		}

		if (!cAF) {
			rAF = function (callback) {
				var currTime = getTime();
				var timeToCall = Math.max(0, 16 - (currTime - lastTime));
				lastTime = currTime + timeToCall;
				return w.setTimeout(function () { callback(currTime + timeToCall); }, timeToCall);
			};

			cAF = function (id) {
				clearTimeout(id);
			};
		}
	}());


	function requestTick() {
		frameId = rAF(requestTick);
		tick();
	}


	function tick() {
		var now = getTime();
		var thisFrameTime = now - time;
		frameTime += (thisFrameTime - frameTime) / SMOOTHING;
		fps = 1000 / frameTime;
		time = now;
	}



	time = getTime();
	requestTick();


	return {
		start: function(){
			if ( !frameId ) {
				requestTick();
			}
		},
		stop: function(){
			cAF(frameId);
			frameId = false;
		},
		get: function(){
			return fps;
		},
		reset: function(){
			frameTime = 0;
		},
		smoothing: function(value){
			SMOOTHING = Math.max(1, value);
		}
	}

});

/*jshint quotmark: false */

define(
'app/3dworld',[
	'jquery',
	'app/Config',
	'hv/net/HTMLLoader',
	'app/3d/World3d.class',
	'hv/animation/AnimationFrame',
	'app/routenetwork/RouteNetworkController.class',
	'app/controllers/Dictionary',
	'app/3d/Elements3d.class',
	'app/content/Navigation',
	'app/modules/RoundMask.class',
	'app/modules/Intro.class',
	'app/modules/GATracker'
],
function(
	$,
	Config,
	Loader,
	World3d,
	AnimationFrame,
	RouteNetworkController,
	Dictionary,
	Elements3d,
	Navigation,
	RoundMask,
	Intro,
	GATracker
) {

	var ns = '.world3d';

	var SPEED = 750;

	var elements;
	var connections;
	var autoroutes;
	var roundmask;

	var c, ctx;
	var windowW, windowH, centerX, centerY;

	var world3d;
	var routenetworkcontroller;
	var animationFrame;

	//swiping
	var startY, isMoved, distY;

	var loader;

	var isTouch = !!('ontouchstart' in window);
	var isWindowFocused;

	var switchPosition;
	var currentView;
	var VIEW_TYPE = { world:"world", routenetwork:"routenetwork", subpage:"subpage" };

	var currentContentEl;
	var buttonPosition;

	var intro;
	var introTimeOutId;
	var introActive = true;

	var KEYCODES = {
		left: 37, up: 38, right: 39, down: 40,
		plus:107, minus:109, zero:96, one:97, two:98, o:79, p:80, m:77, n:78,
		space: 32, escape: 27
	};

	var ignorePopstate = false;


	$(document).on('click', 'a[href]', function(event){
		var href = event.currentTarget.href || $(event.currentTarget).attr('href');

		if (!href || event.isDefaultPrevented()) {
			// we don't want to handle links that have already been prevented by other JS
			return;
		}

		ignorePopstate = true;

		var category = handleLink(href);
		if (category) {
			event.preventDefault();
			// GATracker.replaceLocation(href, category);
		}

		ignorePopstate = false;
	});

	/*
	window.addEventListener('popstate', function(event){
		if (ignorePopstate) return;

		handleLink(location.href);
	}, false);
	*/

	function getPagePath(href) {
		return href ? href.match(/^([^\?#]*)/)[0] : '';
	
	}
	function findElementByHref(href) {
		var id = href.match(/[^#\?]+/)[0];
		var found = false;
		if (href.indexOf(window.location.origin) === 0 && getPagePath(href) !== getPagePath(window.location.href)) { // internal link?
			// loop through all content links and compare href
			$('.element3dlink.js-content-link').each(function(){
				if (this.href === id) {
					found = this;
					return false;
				}
			});
			if (found) {
				var $el = $(found).parents('.element3dcont');
				id = $el.attr('id');
				if (id) {
					return {id: id, el: $el.get(0), link: this};
				}
			}
		}
		return false;
	}

	function handleLink(href) {
		var id, found;


		// test for internal links to flights
		if (href.indexOf('#iata=') >= 0) {
			GATracker.trackEvent('wos-routenetwork-link-click');
			id = href.match(/\#iata=([^&]+)/)[1];
			closeContentPage(function(){
				gotoConnection(id);
			});
			return 'routenetwork';
		}

		id = href.match(/\#([^&\?]+)/);
		id = id && id[1];
		if (id && world3d.findElementIdByHref(id) >= 0) {
			closeContentPage(function(){
				gotoElement(id);
			});
			return 'World';
		}

		// catch internal links to content pages
		// id: http://localhost:3000/html/content-cargo.html#slide=2&autoplay=1 -> http://localhost:3000/html/content-cargo.html
		found = findElementByHref(href);
		if (found) {
			closeContentPage(function(){
				gotoElement(found.id, function(){
					loadPage(href);
				});
			});
			return 'Detail';
		}
		return false;
	}


	//
	// INTRO
	//
	function initPage() {
		intro = new Intro();
		intro.show();
	}

	function onPageLoaded()
	{
		intro.loaded();
		init3dWorld();
		$(window).on("mousewheel", onMouseWheelIntro);
		$(window).on("keyup", onMouseWheelIntro);
		$(window).on("touchmove", onMouseWheelIntro);
		$(window).on("touchstart", onMouseWheelIntro);
		$( ".introinner" ).on("click", onMouseWheelIntro);
		$(".js-navigation-toggle").on("click", onMouseWheelIntro);
		$("#dotsnavigationid").on("click", onMouseWheelIntro);
		$(".js-main-nav__link").on("click",onMouseWheelIntro);


		introTimeOutId = setTimeout( function(){
			onMouseWheelIntro(true);
		}, 10000 );

		onEF( true );

		if (handleLink(window.location.href)) {
			onMouseWheelIntro();
			requestEF();
		} else {
			hideSuffForIntro();
		}

	}


	function showIntro(){
		if (!introActive) {
			intro.show();
			introActive = true;
			world3d.pause();
			$(document).trigger('world3d:intro:show');

		}
	}

	function hideIntro(){
		if (introActive) {
			$(document).trigger('world3d:intro:hide');
			intro.hide();
		}
		introActive = false;
	}

	function onMouseWheelIntro(e) {
		if(e && e.type === 'keyup') {
			// only on arrow keys or spacebar
			if((e.keyCode < 37 || e.keyCode > 40) && e.keyCode !== 32) {
				return false;
			}
		}

		$(window).off("mousewheel", onMouseWheelIntro);
		$(window).off("keyup", onMouseWheelIntro);
		$(window).off("touchmove", onMouseWheelIntro);
		$(window).off("touchstart", onMouseWheelIntro);
		$( ".introinner" ).off("click", onMouseWheelIntro);
		$(".js-navigation-toggle").off("click", onMouseWheelIntro);
		$("#dotsnavigationid").off("click", onMouseWheelIntro);
		$(".js-main-nav__link").off("click",onMouseWheelIntro);

		if(e){
			$(document).trigger('3dworld:goTo3dWorld');
		}

		intro.hide();
		introActive = false;
		
		clearTimeout( introTimeOutId );

		showStuffAfterIntro();

		requestEF();

		controlAutoplay();
	}

	function hideSuffForIntro() {
		//$( "#dotsnavigationid" ).css( { "opacity":"0" } );
		//$( ".js-navigation-toggle" ).css( { "opacity":"0" } );
		$( "#elementscontainerid" ).css( { "opacity":"0" } );
	}

	function showStuffAfterIntro() {
		if(Modernizr.csstransition) {
			$( "#dotsnavigationid" ).css({
				"opacity":"1",
				"transition" : "all 700ms"
			});
			$( ".js-navigation-toggle" ).css({
				"opacity":"1",
				"transition" : "all 700ms"

			});
			$( "#elementscontainerid" ).css({
				"opacity":"1",
				"transition" : "all 700ms"
			});

		} else {
			$( "#dotsnavigationid" ).animate( { "opacity":"1" }, 700 );
			$( ".js-navigation-toggle" ).animate( { "opacity":"1" }, 700 );
			$( "#elementscontainerid" ).animate( { "opacity":"1" }, 700 );
		}
	}
	// intro
	//


	function init3dWorld()
	{
		var $document = $(document),
			$window = $(window);

		c = $('#linescanvasid')[0];
		ctx = c.getContext("2d");

		parseElements();
		parseAutoRoutes();
		parseConnections();

		addAutoRoutesToConnections();

		world3d = new World3d( c, ctx );

		world3d.build( elements, connections, autoroutes );

		var fourthLayerZ = world3d.getFourthLayerZ();

		routenetworkcontroller = new RouteNetworkController( fourthLayerZ );

		world3d.stop();

		loader = new Loader();

		roundmask = new RoundMask();

		new Navigation();

		$document.on('opened.navigation', function() {
			/*world3d.stopWithoutHide();
			routenetworkcontroller.stop();
			// console.log('navigation opened');*/
		});

		onResize();
		$window.resize(function() {
			onResize();
		});

		$window.on('focus blur', function(e) {
			isWindowFocused = (e || event).type === "focus";
		});

		$window.keydown(function( e ) {
			onKeyDown( e );
		});

		$('#js-world3d-container').mousewheel(function( e, delta ) {
			onMouseWheel( e, delta );
		});

		if(navigator.userAgent.match(/(iPad|iPhone|iPod)/g)) {
			$window.on('deviceorientation'+ns, onMacGyroMove );
		}
		else
		{
			$(window).mousemove( function( e ){
				onMouseMove( e );
			});
		}

		if(isTouch) $(".world3d-body")[0].addEventListener('touchstart', onTouchStart, false);
		switchPosition = fourthLayerZ- Elements3d.EL_Z_DIFF;

		$( world3d.c ).bind( "onElement3dLinkClick", function( e, params ) {
			buttonPosition = params.pos;
			getUrl( params.href );
		});

		$document.on('click'+ns, ".js-content-close", function (event) {
			event.preventDefault();
			onContentCloseBtn();
		});

		$('.swiss-logo').on('click'+ns, function(e) {
			if( currentView == VIEW_TYPE.subpage ) {
				e.preventDefault();
				$('.js-content-close').trigger('click');
			}
			$(this).trigger('wos-swiss-logo-click');
		});


	}


	function controlAutoplay() {
		var $elements3d = $('.element3dcont'),
			wasAutoplaying,
			autoplayTimeout,
			mouseLeaveTime = 0,
			delay = 4000;

		$elements3d.on('mouseenter', function() {
			if(autoplayTimeout) {
				clearTimeout(autoplayTimeout);
			}

			if(new Date().getTime() - mouseLeaveTime > delay) {
				wasAutoplaying = !world3d.isPaused();
			}

			world3d.pause();
		});

		$elements3d.on('mouseleave', function() {
			mouseLeaveTime = new Date().getTime();

			if(wasAutoplaying) {
				// start autoplay after n seconds
				autoplayTimeout = setTimeout(function() {
					world3d.unpause();
				}, delay);
			}
		});
	}

	//
	// EVENTS HANDLERS
	//
	function onResize()
	{
		windowW = window.innerWidth;
		windowH = window.innerHeight;

		c.width = windowW;
		c.height = windowH;

		centerX = windowW * 0.5;
		centerY = windowH * 0.5;

		if( world3d )
		{
			world3d.setWindowSize( windowW, windowH );
			world3d.setCenter( centerX, centerY );
			world3d.setBgPos();
		}

		if( routenetworkcontroller )
		{
			routenetworkcontroller.resize( windowW, windowH );
		}
	}


	function onKeyDown( e )
	{
		if( currentView == VIEW_TYPE.subpage ) return;

		var keyCode = e.keyCode || e.which;

		switch (keyCode)
		{
			case KEYCODES.up:
				world3d.gotoNext();
			break;
			case KEYCODES.down:
				world3d.gotoPrev();
			break;
			case KEYCODES.p:
				world3d.unpause();
			break;
			case KEYCODES.n:
				world3d.stop();
			break;
			case KEYCODES.m:
				world3d.play();
			break;
			case KEYCODES.space:
				if ( world3d.isPaused() ) {
					world3d.unpause();
				} else {
					world3d.pause();
				}
			break;
		}
	}


	function onTouchStart( event )
	{
		if( currentView == VIEW_TYPE.subpage) {
			return;
		}

		startY = event.touches[0].clientY;

		isMoved = false;

		$(".world3d-body")[0].addEventListener('touchmove', onTouchMove, false);
		$(".world3d-body")[0].addEventListener('touchend', onTouchEnd, false);
	}


	function onTouchMove( event )
	{
		event.preventDefault();

		distY =  event.touches[0].clientY - startY;

		if( Math.abs( distY ) > 30 ) {
			isMoved = true;
		}
		if ( isMoved ) {
			event.preventDefault();
		}

		world3d.moveCamera( 0, 0, distY*20 );

		startY = event.touches[0].clientY;
	}


	function onTouchEnd( event )
	{
		$(".world3d-body")[0].removeEventListener( 'touchmove', onTouchMove );
		$(".world3d-body")[0].removeEventListener( 'touchend', onTouchEnd );
	}


	function onMouseWheel( e, delta ) {
		if( currentView == VIEW_TYPE.subpage) {
			return;
		}
		//otherwise trackpad on FF/OSX will only fire 1 event
		e.preventDefault();
		var d;

		var o = e.originalEvent,
			w = delta,
			n = 225,
			n1 = n-1;
		d = o.detail,

		// Normalize delta
		d = d ? w && (f = w/d) ? d/f : -d/1.35 : w/120;
		// Quadratic scale if |d| > 1
		d = d < 1 ? d < -1 ? (-Math.pow(d, 2) - n1) / n : d : (Math.pow(d, 2) + n1) / n;
		e.delta = Math.min(Math.max(d / 2, -1), 1);

		d = Math.max(-1, Math.min(1, e.delta)) * 3;

		// on windows
		if(navigator.userAgent.indexOf('Mac OS X') === -1) {
			if( d>0 && d<1) {
				d = 1;
			} else if( d<0 && d>-1 ) {
				d = -1;
			}
		}

		world3d.moveCamera( 0, 0, d * SPEED * -1);

	}


	function onMouseMove( e )
	{
		if( currentView == VIEW_TYPE.subpage ) return;

		var pX = e.pageX / windowW - 0.5;
		var pY = e.pageY / windowH - 0.5;
		world3d.setPositionDif( pX, pY );
	}

	function onMacGyroMove( e )
	{
		if( currentView == VIEW_TYPE.subpage ) return;

		e = e.originalEvent;

		var beta, gamma;

		if (window.orientation !== null) {
			var screenOrientation = window.orientation;

			if (screenOrientation === -90 || screenOrientation == 90) { // landscape
				beta = e.beta;
				gamma = e.gamma;
			} else { // portrait
				beta = e.gamma;
				gamma = e.beta;
			}
		}

		if(beta > 40) {
			beta = 40;
		} else if(beta < -40) {
			beta = -40;
		}

		if(gamma > 40) {
			gamma = 40;
		} else if(gamma < -40) {
			gamma = -40;
		}

		var pX = ( (beta+40)/80 )*1.6;
		var pY = ( (gamma+40)/80 )*1.6;
		world3d.setPositionDif( pX, pY );
	}


	var worldVisible = true;


	function requestEF() {
		if ( !animationFrame ) {
			animationFrame = AnimationFrame.request(onEF);
		} else {
			// console.log('Illegal AnimationFrame request.');
		}
	}

	function cancelEF() {
		AnimationFrame.cancel(animationFrame);
		animationFrame = false;
	}

	function onEF( isOnce ) {

		var isNetworkVisible = false;

		if( isOnce !== true ) {
			animationFrame = false;
			requestEF();
		}

		if( currentView == VIEW_TYPE.subpage ) {
			cancelEF();

			world3d.stop();
			routenetworkcontroller.stop();

			return false;
		}

		var camPos = world3d.getCameraPos();

		if( camPos.z < switchPosition )
		{
			if( currentView != VIEW_TYPE.world )
			{
				world3d.play();
				routenetworkcontroller.stop();
			}

			currentView = VIEW_TYPE.world ;
		}
		else
		{
			if( currentView != VIEW_TYPE.routenetwork )
			{
				world3d.stop();
				routenetworkcontroller.play();
			}

			currentView = VIEW_TYPE.routenetwork;
		}

		world3d.onEF();

		var closestElement = world3d.elements3d.closest;
		if (world3d.camera3d.position.z < 1200) {
			showIntro();
		} else {
			hideIntro();
		}


		if( currentView == VIEW_TYPE.routenetwork )
		{
			isNetworkVisible = routenetworkcontroller.updateCameraPosition( camPos );
		}
		if ( worldVisible == isNetworkVisible ) {
			worldVisible = !isNetworkVisible;
			$('#world3dcontid').css('display', worldVisible ? '' : 'none');
		}
	}
	// events handlers
	//

	//
	// CONTENT
	//
	//

	var worldHref, worldTitle;

	function getUrl( href )
	{
		loadPage( href );
	}


	function loadPage(href, whenLoaded, whenVisible)
	{
		var self = this;

		$("#contentcontainerid").css("display", "block");
		$("#contentbackgroundid").addClass('is-visible');//css("display", "block");

		currentView = VIEW_TYPE.subpage;

		loader.load( href, function( htmlbody, html ) {

			var target = findElementByHref(href);
			if (target) {
				buttonPosition = world3d.elements3d.getLoaderPosition(target.id);
			}

			worldHref = location.href;
			worldTitle = document.title;
			var title = html.match(/<title>([\s\S]+)<\/title>/);
			if (title) {
				document.title = title[1];
			}
			GATracker.replaceLocation(href, 'Detail');

			var $htmlbody = $(htmlbody).filter(".js-content-container");
			var $content = $("#contentinnercontid");

			$content.empty();
			$content.css({"visibility":"hidden"});
			$content.append( $htmlbody );

			setTimeout( function(){initLoadedPage( $htmlbody );}, 100);

			$htmlbody.bind( "content.loaded", function( e ) {
				showLoadedPage(whenVisible);
				if (whenLoaded) whenLoaded($content);
			});
		});
	}

	function showLoadedPage(whenVisible)
	{
		roundmask.show( buttonPosition.left, buttonPosition.top, function(){

			$(document).on('keydown.detailpage', function(event){
				if ( event.keyCode === KEYCODES.escape ) {
					onContentCloseBtn();
				}
			});

			$("#contentbackgroundid").removeClass('is-visible');//.css("display", "none");
			$('#js-world3d-container').css({
				"visibility": "hidden",
				'pointer-events': 'none',
				'display' : 'none'
			});
			$('.js-navigation').css({
				'display':'none'
			});

			if (whenVisible) whenVisible();
		});
		$("#contentinnercontid").css({"visibility":"visible"});
	}

	function initLoadedPage($page)
	{
		var t = $page.data("content-type");

		if( t == "slideshow" ){
			require(['slideshow'], function(page){
				currentContentEl = page;
				currentContentEl.init($page);
			});
		}
		else if( t == "film" ) {
			require(['film'], function(page){
				currentContentEl = page;
				currentContentEl.init($page);
			});
		}
		else if( t == "foldshow" ) {
			require(['foldshow'], function(page){
				currentContentEl = page;
				currentContentEl.init($page);
			});
		}
	}

	function onContentCloseBtn(cb)
	{
		$("#contentinnercontid").trigger('wos-detail-close-click');
		closeContentPage();
	}

	function closeContentPage(whenClosed)
	{
		if (currentView == VIEW_TYPE.subpage) {
			$(document).off('.detailpage');

			roundmask.hide(function(){
				$("#js-world3d-container").css({
					'visibility': 'visible',
					'pointer-events': '',
					'display' : ''
				});
				$('.js-navigation').css({
					'display':''
				});
				$("#contentbackgroundid").removeClass('is-visible');
				onMaskClosingComplete();
				if (whenClosed) whenClosed();
			});

			world3d.hideLoader();
		} else {
			if (whenClosed) whenClosed();
		}
	}


	function onMaskClosingComplete()
	{
		if (currentView == VIEW_TYPE.subpage) {
			requestEF();

			document.title = worldTitle;
			GATracker.replaceLocation(worldHref, 'Detail');

			currentContentEl.destroy();
			currentContentEl = null;
			
			$("#contentinnercontid").empty();
			$("#contentcontainerid").css("display", "none");
			currentView = VIEW_TYPE.world3d;
			world3d.hideLoader();
			$("#contentbackgroundid").removeClass('is-visible');//.css("display", "none");
		}
	}


	/**
	 * Goto route network and open given connection id
	 */
	function gotoConnection( connectionId )
	{
		var els = world3d.elementsData;
		var lastID = els[ els.length - 2].id;
		world3d.gotoElementHref('#'+lastID);
		routenetworkcontroller.openConnection( connectionId );
	}


	/**
	 * Go to element and callback when arrived there
	 */
	var gotoElementInterval, gotoElementTimeout;

	function gotoElement( elementId, whenArrivedAtElement ) {
		world3d.gotoElementHref(elementId);

		cancel();
		if (whenArrivedAtElement) {
			var lastCameraZ = -100000;
			// don't wait forever to arrive at the element ...
			gotoElementTimeout = setTimeout(function(){
				cancel();
			}, 10000);

			gotoElementInterval = setInterval(function(){
				var closestElement = world3d.elements3d.closest && world3d.elements3d.closest.id;
				var cameraZ = world3d.camera3d.position.z;
				if (closestElement === elementId && Math.abs(cameraZ - lastCameraZ) < 5) {
					cancel();
					whenArrivedAtElement(elementId);
				}
				lastCameraZ = cameraZ;
			}, 100);
		}

		function cancel() {
			clearInterval(gotoElementInterval);
			clearTimeout(gotoElementTimeout);
		}
	}


	// content
	//


	//
	// HTML PARSING
	//
	function parseElements()
	{
		elements = [];
		var i;
		var articles = $( "#elementscontainerid .element3dcont" );

		for( i=0; i<articles.length; i++ )
		{
			var article = articles.eq(i);
			var id =  article.attr( 'id' );
			var level =  article.data( 'level' );

			elements.push({
				id:id, level:level, title:$( "h1", article).text(),
				el: article
			});
		}

		// add some invisible elements between the elements so the camera
		// doesn't go up/down immediately after or before the last visible
		// elements
		var l = -1, counter = 0, $dummy = $('<div></div>');
		for (i = elements.length - 1; i >= 0; i--) {
			var el = elements[i];
			if ( el.level != l ) {
				id = 'dummy-'+i;

				if ( l >= 0 ) {
					// $dummy = $('<div class="element3dcont" style="width: 100px; height: 100px; background: red;">'+id+'</div>');
					// $dummy.appendTo('#elementscontainerid');
					elements.splice(i+1, 0, {invisible: true, id: id+'a', level: l, el: $dummy});
				}
				// $dummy = $('<div class="element3dcont" style="width: 100px; height: 100px; background: red;">'+id+'</div>');
				// $dummy.appendTo('#elementscontainerid');
				elements.splice(i+1, 0, {invisible: true, id: id+'b', level: el.level, el: $dummy});
				l = el.level;
			}
		}
	}

	function parseAutoRoutes()
	{
		autoroutes = [];
		var paths = $( "#elementscontainerid .el-item--links" );

		for( var i=0; i<paths.length; i++ )
		{
			autoroutes[i] = [];
			var path = $( "li", paths[i] );

			for( var j=0; j<path.length; j++ )
			{
				autoroutes[i].push( $("a", path[j]).attr("href").substring(1) );
			}
		}
	}

	function parseConnections()
	{
		connections = [];
		var articles = $( "#elementscontainerid .element3dcont" );

		for( var i=0; i<articles.length; i++ )
		{
			var article = $( articles[i] );
			var id1 =  article.attr( 'id' );

			var c = $( ".el-item--related li", article );

			for( var j=0; j<c.length; j++ )
			{
				var id2 = $("a", c[j]).attr("href").substring(1);

				var isThere = false;
				for( var k=0; k<connections.length; k++ )
				{
					if( connections[k].id1 == id2 && connections[k].id2 == id1 )
					{
						isThere = true;
						break;
					}
				}

				if( !isThere ) connections.push( { id1:id1, id2:id2 } );
			}
		}
	}

	function addAutoRoutesToConnections()
	{
		for( var i=0; i<autoroutes.length; i++ )
		{
			var l2 = autoroutes[i].length - 1;
			for( var j=0; j<l2; j++)
			{
				var id1 = autoroutes[i][j];
				var id2 = autoroutes[i][j+1];

				var isThere = false;

				for( var k=0; k<connections.length; k++ )
				{
					if( ( connections[k].id1 == id2 && connections[k].id2 == id1 ) ||
						( connections[k].id1 == id1 && connections[k].id2 == id2 ) )
					{
						isThere = true;
						break;
					}
				}

				if( !isThere ) connections.push( { id1:id1, id2:id2 } );
			}
		}
	}
	// html parsing
	//


	// measure performance (fps)
	// and hide not elementary elements to increase performance
	// once we drop below a reasonable level
	require(['hv/util/fps'], function(f){
		f.smoothing(120);
		var level = 0;
		var inc = 0;
		setInterval(function(){
			if ( !world3d.isRunning() || !isWindowFocused ) {
				f.reset();
				return;
			}
			var fps = f.get();

			//switch off stuff only if the website is slow for 4 following readings (20 seconds)
			if( fps < 15 ) inc++;
			else inc = 0;

			if ( inc > 4 ) {
				switch ( level ) {
					case 0:
						// console.log('Hiding close clouds - fps: '+fps);
						$('.bgnearcont > img').fadeOut('fast');
						level++;
						break;
					case 1:
						// console.log('Hiding background clouds - fps: '+fps);
						$('.bgmidcont > img, .bgfarcont > img').fadeOut('fast');
						level++;
						break;
					case 2:
						// console.log('Hiding clouds - fps: '+fps);
						$('#cloudscontainerid').fadeOut('fast');
						level++;
						break;
					case 3:
						// console.log('Hiding lines - fps: '+fps);
						$('.linescanvascont').fadeOut('fast');
						level++;
						break;
				}
			} else	if ( fps > 55 ) {
				if ( level > 0 ) {
					level--;
				} else {
					return; // do nothing if we're already at zero
				}
				switch ( level ) {
					case 0:
						// console.log('Showing close clouds - fps: '+fps);
						$('.bgnearcont > img').fadeIn();
						break;
					case 1:
						// console.log('Showing background clouds - fps: '+fps);
						$('.bgmidcont > img, .bgfarcont > img').fadeIn();
						break;
					case 2:
						// console.log('Showing clouds - fps: '+fps);
						$('#cloudscontainerid').fadeIn();
						break;
					case 3:
						// console.log('Showing lines - fps: '+fps);
						$('.linescanvascont').fadeIn();
						break;
				}
			}
		},5000);
	});


	var page = {};
	page.init = function(element) {
		this.element = $(element);
		initPage();
	};
	page.onPageLoaded = function() {
		onPageLoaded();
	};

	return page;
});



define(
'app/content/imageHelpers/ImagePreloader',[
	'jquery'
],
function($) {
	function ImagePreloader(src, callback){
		if(src) {
			this.load(src, callback);
		}
	}

	ImagePreloader.prototype.load = function(src, callback){
		var img = new Image();
		img.src = src;

		if (img.complete) {
			done();
		} else {
			$(img).load(done);
		}

		function done(){
			callback && callback(img);
		}
		return img;
	};

	return ImagePreloader;

});

define(
'app/content/imageHelpers/ImageSequence',[
	'jquery', 'app/content/imageHelpers/ImagePreloader'
],
function(
	$, Preloader
) {
	function ImageLibrary(){
		this.library = [];
	}

	ImageLibrary.prototype.load = function(images, callback){
		var lib = this.library;

		for (var i = 0, len = images.length; i < len; i++) {
			lib[i] = false;
			new Preloader(images[i], function(img){
				lib[i] = img;
			});
		};

		callback && callback();
	};

	ImageLibrary.prototype.get = function(index){
		return this.library[index];
	};

	return ImageLibrary;

});

// Created by Hinderling Volkart AG.
// Copyright 2011-2016, Hinderling Volkart AG. All rights reserved.

define('app/content/imageHelpers/ProgressiveImageSequence',[], function() {
	function ProgressiveImageSequence( imgpath , fileExtensionFn , count ,  options ) {
		var myself = this;

		var images = [];
		var numLoaded = 0;
		var isComplete = false;
		this.length = count;


		var defaultOptions = {
			indexSize: 4 ,
			initialStep: 64 ,
			onComplete: null ,
			onProgress: null ,
			stopAt: 1
		};
		var pref = {};
		$.extend(pref,defaultOptions,options);

		var step = pref.initialStep;
		var current = 0;
		var hasRestepped = false;

		function callback( f , o ) {
			if ( !!f ) f.apply(o);
		}

		this.stop = function() {
			step = pref.stopAt / 2;
		};

		this.reset = function() {
			isComplete = false;
			numLoaded = 0;
			step = pref.initialStep;
			current = 0;
			hasRestepped = false;
			this.nearestIndex = -1;
			$.each( images , function(k,v){
				!!v && v.unload();
			});
		};

		this.getAt = function( index ) {
			return images[index].image;
		};

		this.nearestIndex = -1;

		this.getNearest = function( index ) {
			index = Math.floor(index);
			var diff = 0;
			var i,img;
			
			for ( diff = 0; diff <images.length ; diff++ ) {
				i = index+diff;
				if ( i>=0 && i<images.length) {
					img = images[i];
					if ( img && img.isLoaded() ) {
						this.nearestIndex = i;
						return img.image;
					}
				}
				i = index-diff;
				if ( i>=0 && i<images.length) {
					img = images[i];
					if ( img && img.isLoaded() ) {
						this.nearestIndex = i;
						return img.image;
					}
				}
			}
			return null;
		};

		this.getNearestIndex = function() {
			return this.nearestIndex;
		};

		// Loading

		this.getNumLoaded = function() {
			return numLoaded;
		};

		this.getLoadProgress = function() {
			return numLoaded * pref.stopAt / myself.length;
		};

		this.isLoaded = function(index) {
			if ( index === undefined ) {
				return numLoaded == myself.length;
			} else {
				return images[index].isLoaded();
			}
		};

		this.loadPosition = function( position , complete ) {
			position = Math.min( 1 , Math.max(0, position) );
			var index = position * (myself.length-1);
			index = Math.round(index);
			myself.loadIndex(index, complete);
		};

		this.loadIndex = function(index, complete) {
			if ( index < 0 || index >= myself.length ) return false;

			if ( index != Math.floor(index) ) {
				return false;
			}

			//console.log( "Loading " + index + " ("+[current,step]+")" );

			var img = images[index];
			if ( img == null ) {
				var src = getSrcAt(index);
				img = new ImageLoader(src);
				images[index] = img;
			}
			img.load( function() {
				numLoaded++;
				if ( !isComplete ) {
					callback(pref.onProgress,this);
				} else {
					//console && console.log("On progress?");
				}
				callback(complete,this);
			} );
		};

		this.loadNext = function(complete) {
			if ( step < pref.stopAt ) return; // in this case we've already loaded all images - other threads just don't know yet

			function next() {
				loadNextImage();
				callback(complete,this);
			}
			function end() {
				finished();
				callback(complete,this);
			}
			current+=step;
			if ( current >= myself.length ) {
				if ( hasRestepped ) step /= 2;
				hasRestepped = true;
				current = step/2;
				if ( current >= pref.stopAt ) {
					myself.loadIndex(current,next);
				} else {
					finished();
				}
			} else {
				myself.loadIndex(current,next);
			}
		};

		this.getImageLoader = function(index) {
			return images[index];
		};

		var getFileExtension = fileExtensionFn;

		function loadNextImage() {
			setTimeout( function(){ myself.loadNext(); } , 5 );
		}

		function finished() {
			isComplete = true;
			callback(pref.onComplete,this);
			//console.log( "All images loaded" , numLoaded, 'of', myself.length );
		}


		function getSrcAt( index ) {
			var str = (index+Math.pow(10,pref.indexSize)).toString(10).substr(1);

			return (imgpath + getFileExtension(index)).replace( '{index}', str );
		}


		this.load = function() {
			myself.loadIndex(0,loadNextImage);
		}
	}

	return ProgressiveImageSequence;


	function ImageLoader( src ) {
		//var elem = $('<img>');
		this.image = new Image();
		var img = this.image;
		var loadStarted = false;

		this.getSrc = function() {
			return src;
		};

		this.load = function(complete) {
			loadStarted = true;
			img.src = src;
			if ( img.complete ) {
				complete.apply(img);
			} else {
				$(img).load(complete);
			}
		};

		this.unload = function() {
			loadStarted = false;
			//img.src = '';
			img = this.image = new Image();
		};

		this.isLoaded = function() {
			return loadStarted && img.complete;
		}
	}
});


define (
'app/content/cseries/ScrollVideo',[
	'jquery',
	'app/content/BaseModule',
	'app/content/FilmHotspot',
	'app/content/imageHelpers/ImageSequence',
	'app/util/Utils',
	'hv/animation/AnimationFrame',
	'app/content/imageHelpers/ProgressiveImageSequence',
	'app/modules/GATracker'
],
function(
	$,
	BaseModule,
	FilmHotspot,
	ImageSequence,
	Utils,
	AnimationFrame,
	ProgressiveImageSequence
) {
	var ns = '.ScrollVideo';

	var ScrollVideo = function(element) {
		this.$el = $(element);

		this.initVariables();
		this.calculateTotalFrames();
		this.initHotspots();
		this.bindListeners();

		this.preloadImages();

		this.relayout();

		this.bindListeners();
	};

	ScrollVideo.prototype = new BaseModule();

	ScrollVideo.prototype.initVariables = function() {
		this.$window = $(window);

		this.type = $('body').data('type');
		this.$scrollVideoContainer = this.$el.closest('.js-scroll-video-container');

		this.$hotspots = this.$el.find('.js-hotspot');
		this.$img = this.$el.find('.js-scroll-video__image');
		this.img = this.$img[0];
		this.basePath = this.$img.data('base-path');
		this.basePathHighRes = this.$img.data('base-path-high');

		this.fileTypeDefault = this.$img.data('file-type');
		this.fileTypes = this.$img.data('file-types');

		this.lastScroll = 0;

		// make sure it really is parsed to JSON
		this.dataHotspots = this.$el.data('hotspots');
		if(typeof this.dataHotspots === 'object') {
			this.dataHotspots = JSON.stringify(this.dataHotspots);
		}
		this.hotspots = JSON.parse(this.dataHotspots);

		this.dataStops = this.$el.data('stops');
		if(typeof this.dataStops === 'object') {
			this.dataStops = JSON.stringify(this.dataStops);
		}
		this.stops = JSON.parse(this.dataStops);


		this.currentFrame = 0;
		this.totalImages = this.$img.data('total-images');
		this.totalHeight = this.totalImages * 30; /* magic number for now */

		this.recalculate();
	};

	ScrollVideo.prototype.calculateTotalFrames = function() {
		this.totalFrames = this.totalImages;

		for (var i = 0, len = this.stops.length; i < len; i++) {
			var stop = this.stops[i];

			this.totalFrames += stop.duration;
		}
	};

	ScrollVideo.prototype.bindListeners = function() {
		this.$window.on('resize'+ns, this.bind(this.onWindowResize));

		$(document).on('gotoFrame'+ns, this.bind(this.gotoFrame));
	
		$('body').on('click'+ns, '.js-infobox-close', function(e) {
			e.preventDefault();
		});
	};

	ScrollVideo.prototype.initHotspots = function() {
		for (var i = 0, len = this.$hotspots.length; i < len; i++) {
			var $hotspot = this.$hotspots.eq(i),
				hotspotInstance = new FilmHotspot($hotspot);

			$hotspot.data('instance', hotspotInstance);
		}
	};

	ScrollVideo.prototype.gotoFrame = function(e) {
		var self = this,
			frame = e.frame,
			scrollTop = 0,
			maxDuration = 1000,
			framePercentage = (frame / this.totalImages),
			duration = maxDuration * (Math.abs(this.currentFrame - frame) / this.totalFrames);

		scrollTop = this.totalHeight * framePercentage;

		$('body, html').stop(true).animate({
			'scrollTop': scrollTop
		}, Math.round(duration));

		/*setTimeout(function() {
			self.render(frame);
		}, Math.round(duration));*/
	};

	ScrollVideo.prototype.render = function(frame) {
		frame = Math.max(0, frame);

		this.currentFrame = frame;

		if(frame >= this.totalFrames) {
			this.$el.css({
				'display': 'none'
			});
		} else {
			this.$el.css({
				'display': ''
			});
		}

		if(this.currentFrame >= 0 && this.currentFrame <= this.totalFrames) {
			// check for stopping points
			var paintedFrame = this.currentFrame,
				frameOffset = 0;

			for (var i = 0; i < this.stops.length; i++) {
				var stop = this.stops[i],
					startFrame = stop.startFrame + frameOffset;

				if(startFrame < this.currentFrame) {
					// remove or add frames from previous stopping points
					paintedFrame -= stop.duration;
				}

				// check if the current frame is between the range of a stopping point (between startFrame and  startFrame + duration)
				if(this.currentFrame >= startFrame && this.currentFrame <= (startFrame + stop.duration)) {
					paintedFrame = stop.startFrame; // show start frame of the stopping point
				}
				frameOffset += stop.duration;
			}
			this.repaintImage(paintedFrame);
			this.renderHotspots(paintedFrame);
		}

		if(this.type === 'cseries') {
			if(this.currentFrame > this.totalFrames - 30) { // move it out
				this.$el.css({
					'transform': 'translateX('+ (this.elWidth - (this.totalFrames - this.currentFrame) / 30 * this.elWidth) * -1  + 'px) translateZ(0)'
				});
			} else {
				this.$el.css({
					'transform': ''
				});
			}
		}

		this.scheduledAnimationFrame = false;

		return paintedFrame;
	};

	ScrollVideo.prototype.onWindowResize = function() {
		this.recalculate();
		this.relayout();
	};

	ScrollVideo.prototype.recalculate = function() {
		this.windowWidth = this.$window.width();
		this.windowHeight = Math.max(this.$window.height(), (window.innerHeight || document.documentElement.clientHeight || document.body.clientHeight));// Safari Issue

		this.elWidth = this.$el.width();
	};

	ScrollVideo.prototype.relayout = function() {
		this.$scrollVideoContainer.css('height', this.totalHeight);

		this.scaleImage();

		this.$el.trigger('relayout');
	};

	ScrollVideo.prototype.repaintImage = function(frame) {
		var self = this;

		if(this.lastFrame && (frame !== this.lastFrame)) {
			var img = this.imageSeqLoader.getNearest(frame);

			if(img) {
				this.img.src = img.src;
			}
		}
		this.lastFrame = this.currentFrame;

		//load high res image
		clearTimeout(this.loadHighResTimeout);
		this.loadHighResTimeout = setTimeout(function() {
			self.img.src = self.basePathHighRes + Utils.pad(self.imageSeqLoader.getNearestIndex(), 4) + self.getFileExtension(frame);
		}, 200);
	};

	ScrollVideo.prototype.findHotspots = function(currentFrame) {
		var hotspots = this.hotspots,
			activeHotspots = [];

		for (var i = hotspots.length - 1; i >= 0; i--) {
			var hotspot = hotspots[i];

			if(hotspot.startFrame === currentFrame) { // delayed fade in -> hotspot.startFrame + 5
				activeHotspots.push(hotspot);
			}/* else if(hotspot.startFrame <= currentFrame && (hotspot.startFrame + hotspot.frames.length) > currentFrame) { // delayed fade in -> hotspot.startFrame + 5

				activeHotspots.push(hotspot);
			}*/
		}

		return activeHotspots;
	};

	ScrollVideo.prototype.renderHotspots = function(currentFrame) {
		var self = this,
			$activeHotspots = [];

		//if(Utils.isUndefined(this.activeHotspots) || !this.activeHotspots.length > 0) {
			if(this.activeHotspots) {
				for (var i = 0, len = this.activeHotspots.length; i < len; i++) {
					var hotspot = this.activeHotspots[i],
						$hotspot = $(hotspot.id);

				 	$hotspot.addClass('is-hidden').removeClass('hotspot--tooltip-visible');
				}
			}

			this.activeHotspots = this.findHotspots(currentFrame);

			if(this.activeHotspots.length > 0) {
				for (var i = 0, len = this.activeHotspots.length; i < len; i++) {
					var hotspot = this.activeHotspots[i];
					var $hotspot = $(hotspot.id);

					if(hotspot) {
						var hotspotCords = hotspot.frames[(currentFrame - hotspot.startFrame)];

						if(hotspotCords) {
							this.positionAndShowHotspot($hotspot, (hotspotCords.x * this.factorX - 20), (hotspotCords.y * this.factorY - 20));
						} else {
						 	$hotspot.addClass('is-hidden').removeClass('hotspot--tooltip-visible');
							//this.activeHotspots[i] == undefined;

							this.activeHotspots.splice(i, 1);
						}

						//this.lastFrame = this.currentFrame;
					}
				}
			}
	};

	ScrollVideo.prototype.positionAndShowHotspot = function($hotspot, x, y) {
		if(Modernizr.csstransforms3d) {
			$hotspot.css({
				'transform': 'translate(' + x + 'px,' + y + 'px) translateZ(0)'
			}).removeClass('is-hidden').addClass('hotspot--tooltip-visible');
		} else {
			$hotspot.css({
				'top' : y,
				'left' : x
			}).removeClass('is-hidden').addClass('hotspot--tooltip-visible');
		}
	};

	ScrollVideo.prototype.scaleImage = function() {
		var $img = this.$img,
			imageSourceWidth = $img.data('source-width') || 1920,
			imageSourceHeight =  $img.data('source-height') || 1080,
			imageWidth = imageSourceWidth,
			imageHeight = imageSourceHeight,
			maxWidth = $img.data('max-width') || Number.MAX_VALUE,
		    maxHeight = $img.data('max-height') || Number.MAX_VALUE;

		var $offsetParent = $img.parent();

		var scale = Math.max(this.windowWidth / imageWidth, this.windowHeight / imageHeight );

		imageWidth *= scale;
		imageHeight *= scale;

		$offsetParent.css({
			'height' : imageHeight,
			'width' : imageWidth,
			'left' : (this.windowWidth - imageWidth) / 2,
			'top' : (this.windowHeight - imageHeight) / 2
		});

		$img.css({
			/*'height' : '100%',
			'width' : '100%'*/
			'position': 'absolute',
			'top': '50%',
			'left': '50%',
			'transform': 'scale3d(' + [scale, scale, scale].join(',') + ')',
			'width': imageSourceWidth,
			'height': imageSourceHeight,
			'margin-top': imageSourceHeight / 2 * -1,
			'margin-left': imageSourceWidth / 2 * -1
		});

		this.factorY = Utils.round(scale, 2);
		this.factorX = Utils.round(scale, 2);
	};

	ScrollVideo.prototype.getScale = function() {
		return this.factorX;
	};

	ScrollVideo.prototype.getTotalFrames = function() {
		return this.totalFrames;
	};

	ScrollVideo.prototype.getHeight = function() {
		return this.totalHeight;
	};

	ScrollVideo.prototype.getFileExtension = function(index) {
		/*if(index >= 198 && index < 429) {
			return '.jpg';
		}*/

		if (this.fileTypes) {
			for (var i = 0, len = this.fileTypes.length; i < len; i++) {
				var type = this.fileTypes[i];

				if(index >= type.from && index <= type.to) {
					return '.' + type.extension;
				}
			}
		}

		return '.' + this.fileTypeDefault;
	};

	ScrollVideo.prototype.preloadImages = function() {
		var self = this,
			$progressBar = $('.js-scroll-video__loading');

		this.imageSeqLoader = new ProgressiveImageSequence(this.basePath + '{index}', function(index) { return self.getFileExtension(index); }, this.totalImages + 1, {
			indexSize: 4,
			onProgress: function() {
				var progress = self.imageSeqLoader.getLoadProgress() * 100;

				$progressBar.css({
					'width': progress + '%'
				});
			},
			onComplete: function() {
				$('.js-scroll-video__loading').addClass('is-hidden');
			},
			stopAt: 1
		});

		setTimeout(function() {
			self.imageSeqLoader.load();
		}, 30);

	};

	return ScrollVideo;
});

define (
'app/content/cseries/IntroSlide',[
	'jquery', 'app/content/BaseModule', 'app/util/Utils'
],
function(
	$, BaseModule, Utils
) {
	var ns = '.IntroSlide';

	var IntroSlide = function(element) {
		this.$el = $(element);

		this.initVariables();
	};

	IntroSlide.prototype = new BaseModule();

	IntroSlide.prototype.initVariables = function() {
		this.$innerEl = this.$el.find('.js-cseries-intro__inner');

		this.duration = this.$el.data('duration');
		this.textMaxOffset = 20;

		this.$ctoArrows = this.$el.find('.js-cseries-intro__cto-icon__arrows');
		this.ctoMaxOffset = 20;
	};

	IntroSlide.prototype.render = function(currentFrame) {
		if(currentFrame > this.duration) {
			this.$el.addClass('is-hidden');
			return;
		} else {
			this.$el.removeClass('is-hidden');
		}

		var progress = (currentFrame / this.duration);

		this.$el.css({
			'opacity': 1 - progress
		});

		this.$innerEl.css({
			'transform' : 'translateZ(0) translateY(' + (this.textMaxOffset * progress) * -1 + 'px)'
		});

		this.$ctoArrows.css({
			'transform': 'translateZ(0) translateY(' + (this.ctoMaxOffset * progress) + 'px)'
		});
	};

	return IntroSlide;
});

define(
'app/content/imageHelpers/ImageLibrary',[
	'jquery', 'app/content/imageHelpers/ImagePreloader'
],
function(
	$, Preloader
) {
	function ImageLibrary(){
		this.library = [];
	}

	ImageLibrary.prototype.load = function(images, callback){
		var self = this,
			lib = this.library,
			totalImages = images.length;

		for (var i = 0, len = images.length; i < len; i++) {
			lib[i] = false;

			new Preloader(images[i], function(img){
				lib[i] = img;

				totalImages -= 1;

				if(totalImages === 0) {
					callback && callback();
				}
			});
		};

		//callback && callback();
	};

	ImageLibrary.prototype.get = function(index){
		return this.library[index];
	};

	return ImageLibrary;

});

define(
'app/content/cseries/TimelineAjaxHandler',[
	'jquery', 'app/content/BaseModule', 'app/util/Utils', 'hv/animation/AnimationFrame', 'app/content/imageHelpers/ImageLibrary'
],
function(
	$, BaseModule, Utils, AnimationFrame, ImageLibrary
){

	var TimelineAjaxHandler;
	var ns = '.TimelineAjaxHandler';

	TimelineAjaxHandler = function(element){
		var self = this;

		this.$el = $(element);

		this.initVariables();
		this.bindListeners();


		return true;
	};

	TimelineAjaxHandler.prototype = new BaseModule();

	TimelineAjaxHandler.prototype.AJAX_CONTAINER_SELECTOR = '.js-timeline__ajax-container';
	TimelineAjaxHandler.prototype.ENTRIES_SELECTOR = '.js-timeline__days';
	TimelineAjaxHandler.prototype.ENTRY_SELECTOR = '.js-timeline__day';

	TimelineAjaxHandler.prototype.initVariables = function() {
		this.$submitButton = this.$el.find('.js-timeline__more-button');
		this.$entriesContainer = this.$el.find(this.ENTRIES_SELECTOR);
		this.ajaxUrl = this.$el.attr('action');
		this.totalEntries = this.$el.find(this.ENTRY_SELECTOR).length;
		this.maxElements = this.$el.data('max');
	};

	TimelineAjaxHandler.prototype.bindListeners = function() {
		this.$submitButton.on('click'+ns, this.bind(this.onSubmit));
		this.$el.on('change'+ns, this.bind(this.onFilterChange));
		this.$el.on('submit'+ns, this.bind(this.onSubmit));
	};

	TimelineAjaxHandler.prototype.onSubmit = function(e) {
		e.preventDefault();

		this.loadAjaxContent();
	};

	TimelineAjaxHandler.prototype.onFilterChange = function() {
		//scroll to top of timeline
		$('body, html').animate({
			'scrollTop': $('#js-timeline-section').offset().top
		}, 300);

		this.loadAjaxContent('replace');
	};

	TimelineAjaxHandler.prototype.getFormData = function(offset) {
		var data = this.$el.serializeArray();

		data.push({
			'name': 'offset',
			'value': Utils.defaultValue(offset, this.totalEntries)
		});

		data.push({
			'name': 'max',
			'value': this.maxElements
		});

		return data;
	};

	TimelineAjaxHandler.prototype.loadAjaxContent = function(replaceType) {
		replaceType = Utils.defaultValue(replaceType, 'append');

		var self = this;
		var data;

		if(replaceType === 'replace') {
			this.$submitButton.removeClass('is-hidden');

			data = this.getFormData(0);
		} else {
			data = this.getFormData();
		}

		if(this.$xhr) {
			this.$xhr.abort();
		}

		this.$xhr = $.ajax({
			type: 'GET',
			url: this.ajaxUrl,
			data: data,
			dataType: 'html',
			beforeSend: function() {
				if(replaceType === 'replace') {
					self.$entriesContainer.addClass('is-ajax-loading');
				}
			},
			dataFilter: function(data, type) {
				var body = data;

				if ( body.indexOf('<body') >= 0 ) {
					body = data.match(/<body\b[^>]*>([\s\S]*?)<\/body>/gmi)[0];
				}

				return body;
			},
			success: function(data) {
				var $data = $(data),
					$newContent = $data.find(self.ENTRIES_SELECTOR),
					$images = $newContent.find('img'),
					images = [];

				for (var i = 0, len = $images.length; i < len; i++) {
					images.push($images.eq(i).attr('src'));
				}

				var imageLibrary = new ImageLibrary();

				if(images.length > 0) {
					imageLibrary.load(images, function() { // preload images first
						onSucces($newContent);
					});
				} else {
					onSucces($newContent);
				}

				if($data.find('.timeline__more-container').length === 0) {
					$('.timeline__more-container').css({
						'display': 'none'
					});
				} else {
					$('.timeline__more-container').css({
						'display': ''
					});
				}
			}
		});

		function onSucces($newContent) {
			var entryCount = $newContent.find(self.ENTRY_SELECTOR).length;

			if(replaceType === 'replace') {
				self.$entriesContainer.removeClass('is-ajax-loading');
				self.$entriesContainer.html($newContent.html());

				self.totalEntries = 0;
			} else {
				self.$entriesContainer.append($newContent.html());
			}

			setTimeout(function() { /* Todo: wait until image dimensions are available */
				self.$entriesContainer.trigger('timeline_element_added');
			}, 30);

			// update data attributes on form for next call
			self.totalEntries += entryCount;
			self.$el.data('offset', self.totalEntries);

			//show/hide more button
			if($newContent.find('.js-timeline__more-button').length === 0) {
				self.$submitButton.addClass('is-hidden');
			}
		}

	};

	return TimelineAjaxHandler;
});

define(
'app/content/cseries/Timeline',[
	'jquery', 'app/content/BaseModule', 'app/util/Utils', 'hv/animation/AnimationFrame', 'app/content/cseries/TimelineAjaxHandler'
],
function(
	$, BaseModule, Utils, AnimationFrame, TimelineAjaxHandler
){
	var Timeline;
	var ns = '.timeline';

	Timeline = function(element){
		var self = this;
		
		this.$el = $(element);

		this.initVariables();
		this.bindListeners();

		this.relayout();
		this.$el.addClass('is-loaded');

		this.timelineAjaxHandler = new TimelineAjaxHandler('.js-timeline__ajax-container');

		return true;
	};

	Timeline.prototype = new BaseModule();

	Timeline.prototype.initVariables = function() {
		this.$window = $(window);

		//this.$timelineLine = this.$el.find('.js-timeline__line');
		this.$timelineFilterContainer = $('.js-timeline__filter-container');
		this.$days = this.$el.find('.js-timeline__day');

		this.recalculate();
	};

	Timeline.prototype.bindListeners = function() {
		var self = this;
		this.$window.on('resize'+ns, Utils.debounce(this.onWindowResize.bind(this), 200));
		this.$window.on('scroll'+ns, this.onScroll.bind(this));

		this.$el.on('timeline_element_added', this.bind(this.onElementsAdded));
	};

	Timeline.prototype.onWindowResize = function() {
		this.recalculate();
		this.relayout();
	};

	Timeline.prototype.onScroll = function(e) {
		var self = this,
			scrollTop = this.$window.scrollTop();

		if(self.scheduledAnimationFrame) {
			return;
		}
		self.scheduledAnimationFrame = true;

		AnimationFrame.request(function() {
			self.render(scrollTop);
		});
	};

	Timeline.prototype.render = function(scrollTop) {
		scrollTop = Utils.defaultValue(scrollTop, this.$window.scrollTop());

		var self = this,
			triggerPosition = this.windowHeight * 0.8,
			relScrollTop = Math.max(scrollTop + triggerPosition - this.timelineOffsetTop, 0),
			lineHeight = Math.min(relScrollTop, this.timelineHeight);

		if(scrollTop > self.timelineOffsetTop - (self.windowHeight) && scrollTop < self.timelineBottom) {
			self.$timelineFilterContainer.addClass('is-visible');
		} else {
			self.$timelineFilterContainer.removeClass('is-visible');
		}

		/*self.$timelineLine.css({
			'height': 1,
			'transform': 'translateZ(0) scaleY(' + Math.round(lineHeight) + ')'
		});*/

		// fade in/out timeline day labels
		for (var i = 0, len = this.timelineDays.length; i < len; i++) {
			var timelineDayLabelItem = this.timelineDays[i];

			if(timelineDayLabelItem.top <= lineHeight) {
				timelineDayLabelItem.$label.addClass('is-visible');
				timelineDayLabelItem.$entries.addClass('is-visible');
			} else {
				timelineDayLabelItem.$label.removeClass('is-visible');
				timelineDayLabelItem.$entries.removeClass('is-visible');
			}
		}

		self.scheduledAnimationFrame = false;
	};

	Timeline.prototype.recalculate = function() {
		this.windowWidth = this.$window.width();
		this.windowHeight = this.$window.height();

		this.elWidth = this.$el.outerWidth();
		this.timelineOffsetTop = this.$el.offset().top;
		this.timelineBottom = this.timelineOffsetTop + this.$el.innerHeight() - 200;

		this.timelineHeight = this.$el.height();

		this.initTimelineDayLabelItems();
	};

	Timeline.prototype.initTimelineDayLabelItems = function() {
		this.$timelineDays = this.$el.find('.js-timeline__day');
		this.timelineDays = [];

		for (var i = 0, len = this.$timelineDays.length; i < len; i++) {
			var $timelineDay = this.$timelineDays.eq(i),
				$timelineDayLabel = $timelineDay.find('.js-timeline__day__title');

			this.timelineDays.push({
				'$label': $timelineDayLabel,
				'$entries': $timelineDay.find('.js-timeline__entry'),
				'top': Math.round($timelineDayLabel.offset().top - this.timelineOffsetTop)
			});
		}
	};

	Timeline.prototype.onElementsAdded = function() {
		var self = this;
		this.$days = this.$el.find('.js-timeline__day');

		self.forceRelayout();
		self.render();
	};

	Timeline.prototype.forceRelayout = function() {
		this.relayout(true);
	};

	Timeline.prototype.relayout = function(forceRelayout) {
		forceRelayout = Utils.defaultValue(forceRelayout, false);


		// console.time('relayout');
		// only execute if width has changed
		if(forceRelayout || (!Utils.isAssigned(this.lastElWidth) || this.lastElWidth !== this.elWidth)) {
			this.timelineEntries = [];

			var totalHeight = 0,
				lastDayPositionBottom = 0;

			// loop over all days
			for (var i = 0, len = this.$days.length; i < len; i++) {
				var $dayItem = this.$days.eq(i),
					$entries = $dayItem.find('.js-timeline__entry'),
					top = 0,
					dayPaddingTop = 0;

				// loop over all entries per day
				for (var j = 0, lenJ = $entries.length; j < lenJ; j++) {
					var $entry = $entries.eq(j),
						entryHeight = $entry.outerHeight(true);

					if(j === 0) {
						// position entry based on the "arrow"
						var $contentContainer = $entry.find('.js-timeline__entry__content-container'),
							contentContainerPosTop = Math.round($contentContainer.position().top),
							$arrow = $entry.find('.js-timeline__entry__arrow'),
							arrowPosTop = 24,
							offsetTop = contentContainerPosTop + arrowPosTop;

						if(i === 0) {
							top -= offsetTop;
						}
						if(i > 0) {
							if(lastDayPositionBottom > offsetTop) {
								top = lastDayPositionBottom - offsetTop;
							}

							dayPaddingTop = Math.round(Math.max(offsetTop, lastDayPositionBottom));
							$dayItem.css({
								'padding-top' : dayPaddingTop
							});
						}

						// make sure first element in timeline allways is visible (set margin-top on container)
						if(i === 0 && j === 0) {
							this.$el.css({
								'margin-top' : offsetTop + 40
							});
						} else if(i === len - 1 && j === lenJ - 1) { // and same on last element
							this.$el.css({
								'margin-bottom' : entryHeight - offsetTop
							});
						}
					}

					$entry.css({
						'top': top
					});

					top += entryHeight;
					lastDayPositionBottom = top - dayPaddingTop;
					totalHeight += lastDayPositionBottom;
				}
			}

			// lines
			/*for (var i = 0, len = this.$days.length; i < len; i++) {
				var $day = this.$days.eq(i);

			}*/

			this.lastElWidth = this.elWidth;

			if(this.$days.length === 0) {
				this.$el.css({
					'margin-top': '0',
					'margin-bottom': '0'
				});
			}

			this.recalculate();
			// console.timeEnd('relayout');

			return true;
		} else {
			// console.timeEnd('relayout');

			return false;
		}
	};

	Timeline.prototype.destroy = function() {
		this.$el.off(ns);

		$(window).off(ns);
		$(document).off(ns);

		this.$el = undefined;
	};

	return Timeline;
});

define (
'app/content/BarChart',[
	'jquery', 'app/content/BaseModule', 'app/util/Utils'
],
function(
	$, BaseModule, Utils
) {
	var ns = '.BarChart';

	var BarChart = function(element) {
		this.$el = $(element);
		
		this.initVariables();

		this.repaint();
	
		this.bindListeners();
	};

	BarChart.prototype = new BaseModule();

	BarChart.prototype.initVariables = function() {
		this.$lines = this.$el.find('.js-barchart__bar');
		this.$gridLine = this.$el.find('.js-barchart__gridline').remove().clone();

		this.maxValue = this.$el.data('max-value');
		this.gridSteps = this.$el.data('grid-steps');

		this.elWidth = this.$el.width();
		this.lastElWidth = 0;
	};

	BarChart.prototype.bindListeners = function() {
		$(window).on('resize'+ns, Utils.debounce(this.bind(this.onWindowResize), 200));
	};

	BarChart.prototype.onWindowResize = function() {
		this.lastElWidth = this.elWidth;
		this.elWidth = this.$el.width();

		this.repaint();
	};

	BarChart.prototype.repaint = function() {
		if(this.elWidth !== this.lastElWidth) {
			var left = this.$el.width() / 2,
				lineWidth = this.$lines.first().width();

			left -= (this.$lines.length * lineWidth) / 2;

			// paint lines
			for (var i = 0, len = this.$lines.length; i < len; i++) {
				var $line = this.$lines.eq(i),
					value = $line.data('value');
				$line.css({
					'height': value / this.maxValue * 100 +'%',
					'left': left
				});

				left += $line.outerWidth(true);
			}

			// paint grid
			var bottom = 0,
				gridLineSpacing = Math.round((this.$el.height() + (Math.round(this.$el.height() / this.gridSteps))) / this.gridSteps);

			// remove old lines
			this.$el.find('.js-barchart__gridline').remove();

			for (var j = 0, lenJ = this.gridSteps; j < lenJ; j++) {
				var $gridLine = this.$gridLine.clone();

				$gridLine.css({
					'bottom': bottom
				});

				this.$el.append($gridLine);
				
				bottom += gridLineSpacing;
			}
		}
	};

	return BarChart;
});

define (
'app/content/cseries/FlyingText',[
	'jquery', 'app/content/BaseModule', 'app/util/Utils'
],
function(
	$, BaseModule, Utils
) {
	var ns = '.FlyingText';

	var FlyingText = function(element) {
		this.$el = $(element);

		this.initVariables();

		if(Utils.isDefined(this.scale)) {
			this.relayout();
		}
	};

	FlyingText.prototype = new BaseModule();

	FlyingText.prototype.initVariables = function() {
		this.visibleFrame = this.$el.data('visible-frame');
		//this.visibleDuration = this.$el.data('visible-duration');

		this.scaleFactor = 1; /* scale of airplane image*/
		this.position = this.$el.data('position');

		this.showAnimationDuration = Utils.defaultValue(this.$el.data('show-duration'), 50);
		this.hideAnimationDuration = Utils.defaultValue(this.$el.data('hide-duration'), 30);

		this.maxScale = Utils.defaultValue(this.$el.data('max-scale'), 3);
		this.minScale = Utils.defaultValue(this.$el.data('min-scale'), 0.7);
		this.showMaxOffsetX = Utils.defaultValue(this.$el.data('show-max-offset-x'), -70);
		this.hideMaxOffsetX = Utils.defaultValue(this.$el.data('hide-max-offset-x'), -40);
	};

	FlyingText.prototype.render = function(currentFrame, effectiveFrame) {
		var relFrame,
			progress,
			scale,
			opacity;

		if(currentFrame === this.visibleFrame) {
			this.$el.addClass('is-visible').css({
				'visibility': '',
				'display': '',
				'opacity': '',
				'transform': ''
			});
		} else if(currentFrame >= (this.visibleFrame - this.showAnimationDuration) && currentFrame < this.visibleFrame) {
			relFrame = (this.showAnimationDuration - this.visibleFrame) + currentFrame;
			progress = 1 - relFrame / this.showAnimationDuration;
			scale = 1 + ((this.maxScale - 1) * progress);
			opacity = relFrame / (this.showAnimationDuration - (this.showAnimationDuration / 2));

			this.$el.addClass('is-visible').css({
				'visibility': 'visible',
				'display': 'block',
				'opacity': opacity,
				'transform': 'scale3d(' + [scale, scale, scale].join(',') + ') translateX(' + this.showMaxOffsetX * progress + 'px)',
				'transform-origin' : 'left bottom'
			});
		} else if(currentFrame <= (this.visibleFrame + this.hideAnimationDuration) && currentFrame >= this.visibleFrame) {
			relFrame = (this.hideAnimationDuration - this.visibleFrame) + currentFrame - this.hideAnimationDuration;
			progress = relFrame / this.hideAnimationDuration;
			scale = 1 + ((this.minScale - 1) * progress);
			opacity = 1 - relFrame / (this.hideAnimationDuration - (this.hideAnimationDuration / 2));

			this.$el.addClass('is-visible').css({
				'visibility': 'visible',
				'display': 'block',
				'transform': 'scale3d(' + [scale, scale, scale].join(',') + ') translateX(' + this.hideMaxOffsetX * progress + 'px)',
			//	'transform-origin' : 'center bottom',
				'opacity' : opacity
			});
		} else {
			this.$el.removeClass('is-visible').css({
				'visibility': '',
				'display': '',
				'opacity': '',
				'transform': ''
			});
		}
	};

	FlyingText.prototype.setScale = function(value) {
		this.scaleFactor = value;
		this.relayout();
	};

	FlyingText.prototype.relayout = function() {
		this.$el.css({
			'left': this.position[0] * this.scaleFactor,
			'top': this.position[1] * this.scaleFactor
		});
	};

	return FlyingText;
});

define(
'app/content/cseries/AirplaneDimension',[
	'jquery', 'app/content/BaseModule', 'app/util/Utils'
],
function(
	$, BaseModule, Utils
){

	var AirplaneDimension;
	var ns = '.AirplaneDimension';

	AirplaneDimension = function(element){
		var self = this;

		this.$el = $(element);

		this.initVariables();

		return true;
	};

	AirplaneDimension.prototype = new BaseModule();

	AirplaneDimension.prototype.initVariables = function() {
		this.$window = $(window);

		this.visibleFrame = this.$el.data('visible-frame');

		this.top = this.$el.data('top');
		this.left = this.$el.data('left');
		this.width = this.$el.data('width');
		this.height = this.$el.data('height');

	};

	AirplaneDimension.prototype.render = function(currentFrame) {
		if(this.visibleFrame === currentFrame) {
			this.show();
		} else {
			this.hide();
		}
	};

	AirplaneDimension.prototype.show = function() {
		var self = this;

		this.showTimeout = setTimeout(function() {
			self.$el.addClass('is-visible');
		}, 50);
	};

	AirplaneDimension.prototype.hide = function() {
		clearTimeout(this.showTimeout);

		this.$el.removeClass('is-visible');
	};

	AirplaneDimension.prototype.relayout = function() {
		this.$el.css({
			'top': this.top * this.scale,
			'left': this.left * this.scale,
			'width': this.width * this.scale,
			'height': this.height * this.scale
		});
	};

	AirplaneDimension.prototype.resize = function() {
		this.relayout();
	};

	AirplaneDimension.prototype.setScale = function(scale, offsetLeft) {
		this.scale = scale;
		this.offsetLeft = offsetLeft;
		this.relayout();
	};

	return AirplaneDimension;
});

define (
'app/content/cseries/OutroSlide',[
	'jquery', 'app/content/BaseModule', 'app/util/Utils'
],
function(
	$, BaseModule, Utils
) {
	var ns = '.OutroSlide';

	var OutroSlide = function(element) {
		this.$el = $(element);

		this.initVariables();
		this.bindListeners();
		this.relayout();
	};

	OutroSlide.prototype = new BaseModule();

	OutroSlide.prototype.initVariables = function() {
		this.$window = $(window);

		this.recalculate();
	};

	OutroSlide.prototype.bindListeners = function() {
		this.$window.on('resize'+ns, this.bind(this.onWindowResize));
	};

	OutroSlide.prototype.onWindowResize = function(first_argument) {
		this.recalculate();
		this.relayout();
	};

	OutroSlide.prototype.recalculate = function() {
		this.windowHeight = this.$window.height();
	};

	OutroSlide.prototype.relayout = function() {
		this.$el.css({
			'min-height': this.windowHeight
		});
	};

	return OutroSlide;
});

define (
'app/content/cseries/BackgroundClouds',[
	'jquery', 'app/content/BaseModule', 'app/util/Utils'
],
function(
	$, BaseModule, Utils
) {
	var ns = '.BackgroundClouds';

	var BackgroundClouds = function(element) {
		this.$el = $(element);

		this.initVariables();
		this.bindListeners();

		this.positionClouds();
	};

	BackgroundClouds.prototype = new BaseModule();

	BackgroundClouds.prototype.initVariables = function() {
		this.$window = $(window);

		this.$scrollVideo = $('.js-scroll-video-container');

		this.$transitionClouds = $('.js-transition-clouds');

		// get clouds
		this.$cloudsTimelineEl = $('.js-static-elements-container');
		this.$cloudsTimeline = this.$el.find('.js-bg-clouds__timline');
		this.cloudsTimelineDuration = 500;

		this.$cloudsOutro = this.$el.find('.js-bg-clouds__outro');

		this.$transitionCloudNear = $('.js-transition-cloud--near');
		this.$transitionCloudMid = $('.js-transition-cloud--mid');

		this.$timelineClouds = $('.js-bg-clouds__timline');

		this.$clouds1 = $('.js-transition-cloud--intro');
		this.$clouds2 = $('.js-transition-cloud--milestones');
		this.$clouds3 = $('.js-transition-cloud--timeline');

		this.recalculate();
	};

	BackgroundClouds.prototype.positionClouds = function() {
		var $clouds = $('.js-transition-cloud');

		for (var i = 0; i < $clouds.length; i++) {
			var $cloud = $clouds.eq(i);

			$cloud.css({
				'margin-top': $cloud.height() * -0.5
			});
		}
	};

	BackgroundClouds.prototype.bindListeners = function() {
		this.$scrollVideo.on('relayout'+ns, this.bind(this.recalculateScrollVideoEnd));
	};

	BackgroundClouds.prototype.recalculate = function() {
		this.windowHeight = this.$window.height();
		this.docHeight = $(document).height();

		this.scrollVideoHeight = this.$scrollVideo.height();
		this.timelineStart = this.scrollVideoHeight;

		this.cloudsTimelineElHeight = this.$cloudsTimelineEl.height();
		this.cloudsTimelineHeight = this.$cloudsTimeline.height();

		this.cloudsOutroHeight = this.$cloudsOutro.height();
		this.cloudsOutroDuration = 1000;
		this.cloudsOutroTriggerPosition = $('.js-cseries-outro').offset().top - 200 - this.windowHeight;


		this.scrollVideoEndTransitionStart = this.scrollVideoHeight - this.windowHeight - (this.windowHeight / 2);
		this.scrollVideoEndTransitionDuration = this.windowHeight;
		this.scrollVidoeEndTransitionMaxMoveY = this.$transitionCloudNear.height();

		this.recalculateScrollVideoEnd();
	};

	BackgroundClouds.prototype.recalculateScrollVideoEnd = function() {
		this.scrollVideoEnd = this.scrollVideoHeight * 0.88;
	};

	BackgroundClouds.prototype.render = function(scrollTop, currentFrame, imageFrame) {

		// intro clouds
		if(imageFrame > 10 && imageFrame < 425) {
			var progress = Math.max(0, 1 - (100 / (currentFrame - 10)));

			this.$clouds1.css({
				'transform': 'translateY(' + progress * ($(window).height()) + 'px) translateZ(0) scale(' + (1 + progress / 2) + ')',
				'visibility':'visible'
			});

			this.$clouds2.css({
				'transform': 'scale(' + (1 + progress) * 1.1 + ')',
				'visibility': 'visible'
			});
		} else if(imageFrame > 500) {
			var progress = Math.min(500 - imageFrame / this.scrollVideoEndTransitionDuration, 1),
				scale = Math.max((3 + (1 * progress)), 1);

			this.$clouds1.css({
				'transform': 'translateY(' + progress * this.windowHeight * - 1.2 + 'px) translateZ(0) scale('+ scale - 0.5 +')',
				'z-index': '10000',
				'visibility': 'visible'
			});
			this.$clouds3.css({
				'visibility': 'visible',
				'transform': 'translateY(' + progress * this.$clouds2.height() * - 1 + 'px) translateZ(0) scale('+ scale * 0.5 +')',
				'transform-origin': 'center bottom'
			});
		} else {
			this.$clouds1.css({
				'visibility': 'visible'
			});
			this.$clouds2.css({
				'visibility': 'visible'
			});
		}

		if(imageFrame > 428) {
			this.$timelineClouds.addClass('is-visible');
		} else {
			this.$timelineClouds.removeClass('is-visible');
		}
	};

	return BackgroundClouds;
});

define (
'app/content/cseries/CSeriesPager',[
	'jquery', 'app/content/BaseModule', 'app/util/Utils'
],
function(
	$, BaseModule, Utils
) {
	var ns = '.CSeriesPager';

	var CSeriesPager = function(element) {
		this.$el = $(element);

		this.$pagers = this.$el.find('.js-slideshow__pager__link');

		this.initPagers();

		this.bindListeners();
	};

	CSeriesPager.prototype = new BaseModule();

	CSeriesPager.prototype.bindListeners = function() {
		this.$el.on('click'+ns, '.js-slideshow__pager__link', this.bind(this.onPagerClick));
	};

	CSeriesPager.prototype.initPagers = function() {
		this.pagers = [];

		for (var i = 0, len = this.$pagers.length; i < len; i++) {
			var $pager =  this.$pagers.eq(i);
			var lastFrame;

			if(i < len - 1) {
				lastFrame = this.$pagers.eq(i + 1).data('frame');
			} else {
				lastFrame = $pager.data('frame') + 1;
			}

			this.pagers.push({
				'$el': $pager,
				'frame': $pager.data('frame'),
				'index': $pager.data('index'),
				'lastFrame': lastFrame
			});
		}

		this.setActivePager(0);
	};

	CSeriesPager.prototype.onPagerClick = function(e) {
		this.$el.find('a.is-active').removeClass('is-active');

		var $activePager = $(e.currentTarget),
			activePagerIndex = $activePager.data('index');

		this.setActivePager(activePagerIndex);

		this.$el.trigger({
			'type':	'gotoFrame',
			'frame': $activePager.data('frame')
		});
	};

	CSeriesPager.prototype.render = function(frame) {
		frame = Math.max(0, frame);

		for (var i = 0, len = this.pagers.length; i < len; i++) {
			if((frame >= this.pagers[i].frame && frame < this.pagers[i].lastFrame) || i+1 === len) {
				if(i === this.activeIndex) {
					return;
				}

				this.setActivePager(this.pagers[i].index);
				return;
			}
		};
	};

	CSeriesPager.prototype.setActivePager = function(index) {
		var $activePager = this.$pagers.eq(index),
			$activePagerCircle = $('.active-pager-circle');

		this.activeIndex = index;

		$activePagerCircle.css({
			'top' : $activePager.position().top,
			'transition' : 'all 200ms linear'
		});
	};

	return CSeriesPager;
});

define (
'app/content/cseries/CSeriesController',[
	'jquery',
	'app/content/BaseModule',
	'app/util/Utils',
	'hv/animation/AnimationFrame',
	'app/content/cseries/ScrollVideo',
	'app/content/cseries/IntroSlide',
	'app/content/cseries/Timeline',
	'app/content/BarChart',
	'app/content/cseries/FlyingText',
	'app/content/cseries/AirplaneDimension',
	'app/content/cseries/OutroSlide',
	'app/content/cseries/BackgroundClouds',
	'app/content/cseries/CSeriesPager',
	'app/content/Slideshow'
],
function(
	$,
	BaseModule,
	Utils,
	AnimationFrame,
	ScrollVideo,
	IntroSlide,
	Timeline,
	BarChart,
	FylingText,
	AirplaneDimension,
	OutroSlide,
	BackgroundClouds,
	CSeriesPager,
	Slideshow
) {
	var ns = '.CSeriesController';
	var instance; /* singleton impl. */

	var CSeriesController = function() {
		this.initVariables();
		this.bindListeners();
		this.relayout();
	};

	CSeriesController.prototype = new BaseModule();

	CSeriesController.prototype.initVariables = function() {
		this.lastProgress = 0;

		this.scrollVideo = new ScrollVideo('.js-scroll-video');
		this.introSlide = new IntroSlide('.js-cseries-intro');

		this.flyingTexts = this.initFlyingTexts();
		this.airplaneDimensions = this.initAirplaneDimensions();

		var $timeline = $('.js-timeline');
		if($timeline.length) {
			this.timeline = new Timeline($timeline);
		}

		this.outroSlide = new OutroSlide('.js-cseries-outro');

		this.pager = new CSeriesPager('.js-cseries-pager');

		this.$scrollVideoContainer = $('.js-scroll-video-container');
		this.$timelineContainer = $('.js-static-elements-container');

		this.$window = $(window);

		this.recalculate();

		this.initBarCharts();

		var $backgroundClouds = $('.js-bg-clouds-container');
		if($backgroundClouds.length > 0) {
			this.backgroundClouds = new BackgroundClouds($backgroundClouds);
		}

		$('html').addClass('is-initialized');

		var $slide = $('.js-slideshow-container');
		if($slide.length) {
			new Slideshow();
		}
	};

	CSeriesController.prototype.initFlyingTexts = function() {
		var $flyingTexts = $('.js-flying-text'),
			scale = this.scrollVideo.getScale(),
			instances = [];

		if($flyingTexts.length > 0) {
			for (var i = 0, len = $flyingTexts.length; i < len; i++) {
				var flyingText = new FylingText($flyingTexts.eq(i));

				flyingText.setScale(scale);
				instances.push(flyingText);
			}
		}

		return instances;
	};

	CSeriesController.prototype.initBarCharts = function() {
		var $barCharts = $('.js-barchart');

		if($barCharts.length > 0) {
			for (var i = 0, len = $barCharts.length; i < len; i++) {
				new BarChart($barCharts.eq(i));
			}
		}
	};

	CSeriesController.prototype.initAirplaneDimensions = function() {
		var $airplaneDimensions = $('.js-airplane_dimension'),
			scale = this.scrollVideo.getScale(),
			instances = [];

		if($airplaneDimensions.length > 0) {
			for (var i = 0, len = $airplaneDimensions.length; i < len; i++) {
				var airplaneDimension = new AirplaneDimension($airplaneDimensions.eq(i));
				airplaneDimension.setScale(scale);

				instances.push(airplaneDimension);
			}
		}

		return instances;
	};

	CSeriesController.prototype.recalculate = function() {
		this.windowHeight = this.$window.height();

		this.scrollVideoHeight = this.scrollVideo.getHeight();
		this.scrollVideoTotalFrames = this.scrollVideo.getTotalFrames();
	};

	CSeriesController.prototype.relayout = function() {
		this.$timelineContainer.css({
			'height': this.timelineContainerHeight,
			'min-height': this.windowHeight
		});
	};

	CSeriesController.prototype.bindListeners = function() {
		this.$window.on('scroll'+ns, this.bind(this.onScroll));
		// this.date = new Date().getTime();
		this.$window.on('resize'+ns, this.bind(this.onWindowResize));
	};

	CSeriesController.prototype.renderLoop = function() {
		// calculate frame
		var scrollTop = this.$window.scrollTop(),
			scrollVideoProgress = ((scrollTop) / (this.scrollVideoHeight - this.windowHeight));

		if (!this.scrollVideoProgress) this.scrollVideoProgress = 0;
		this.scrollVideoProgress += (scrollVideoProgress - this.scrollVideoProgress) / 12;

		/*var newProgress = ((scrollTop) / (this.scrollVideoHeight - this.windowHeight));
		var progress = this.lastProgress +  (newProgress - this.lastProgress) / 15;*/

		this.currentFrame = Math.round(this.scrollVideoTotalFrames * this.scrollVideoProgress);

		// render all components
		var imageFrame = this.scrollVideo.render(this.currentFrame); // imageFrame = current img number

		imageFrame = Utils.defaultValue(imageFrame, this.currentFrame);

		this.introSlide.render(imageFrame);

		var i, len;
		for (i = 0, len = this.flyingTexts.length; i < len; i++) {
			this.flyingTexts[i].render(imageFrame, this.currentFrame);
		}
		for (i = 0, len = this.airplaneDimensions.length; i < len; i++) {
			this.airplaneDimensions[i].render(imageFrame);
		}

		if(this.backgroundClouds) {
			this.backgroundClouds.render(scrollTop, this.currentFrame, imageFrame);
		}

		this.pager.render(this.currentFrame);

		//this.lastProgress = progress;

		// reset for next animation frame
		this.scheduledAnimationFrame = false;

		if (Math.round(this.scrollVideoTotalFrames * scrollVideoProgress) !== this.currentFrame) {
			this.scheduledAnimationFrame = setTimeout(this.bind(this.renderLoop),16);
		}
	};

	CSeriesController.prototype.onWindowResize = function() {
		var i, len, scale;

		this.recalculate();
		this.relayout();

		scale = this.scrollVideo.getScale();

		for (i = 0, len = this.airplaneDimensions.length; i < len; i++) {
			this.airplaneDimensions[i].setScale(scale);
		}
		for (i = 0, len = this.flyingTexts.length; i < len; i++) {
			this.flyingTexts[i].setScale(scale);
		}
	};

	CSeriesController.prototype.onScroll = function() {
		var scrollTop = this.$window.scrollTop(),
			self = this;

		 // prevent multiple rAF callbacks.
		if(self.scheduledAnimationFrame) {
			return;
		}

		if(scrollTop > this.lastScroll) {
			scrollDirection = 'down';
		} else {
			scrollDirection = 'up';
		}

		self.scheduledAnimationFrame = AnimationFrame.request(this.bind(this.renderLoop));
		this.lastScroll = scrollTop;
	};

	return function getInstance () {
		return (instance = (instance || new CSeriesController()));
	};
});

define('cseries',['app/content/cseries/CSeriesController', 'vendor/fastclick', 'mousewheel'], function(CSeriesController, FastClick){

	var cseriesController;
	function initPage() {
		if ( FastClick && FastClick.attach ) {
			FastClick.attach(document.body);
		}
		cseriesController = new CSeriesController();
	}
	function destroyPage() {
		cseriesController.destroy();
	}

	var page = {};
	page.init = function(element) {
		this.element = $(element);
		initPage();
	};
	page.destroy = function() {
		destroyPage();
	};

	return page;
});

/*!
 * World of Swiss
 * Copyright 2015 Hinderling Volkart AG and Swiss Airlines Ltd.
 * http://hinderlingvolkart.com
 *
 * Authors: Tomasz Slawnikowski, Severin Klaus, Dario Merz, Adonis Bou Chakra, Gunisigi Balaban
 * Authors: Tomasz Slawnikowski, Severin Klaus, Dario Merz, Adonis Bou Chakra, Gunisigi Balaban
 */


requirejs.config({
	waitSeconds: 30,
	
	paths: {
		jquery: 'vendor/jquery',
		tpl: 'vendor/require/tpl',
		mousewheel: 'vendor/jquery-plugins/jquery.mousewheel',

		jqueryeasing: 'vendor/jquery-plugins/jquery.easing.1.2'

	},

	//urlArgs: "bust=" + (new Date()).getTime(),

	shim: {
		'jquery': { exports: 'jQuery' },
		'app/plugins': { deps: ['jquery'] },
		'mousewheel': { deps: ['jquery'] },
		'jqueryeasing': { deps: ['jquery'] }
	}
});


// make it safe to use console.log always
(function(a){function b(){}for(var c="assert,count,debug,dir,dirxml,error,exception,group,groupCollapsed,groupEnd,info,log,markTimeline,profile,profileEnd,time,timeEnd,trace,warn".split(","),d;!!(d=c.pop());){a[d]=a[d]||b;}})
(function(){try{console.log();return window.console;}catch(a){return (window.console={});}}());


require( ['jquery', 'hv/util/log', 'app/Config', 'app/plugins', 'mousewheel', 'app/modules'],
	function($, log, Config){

	if (typeof console == "undefined" || typeof console.log == "undefined") var console = { log: function() {} };

	// forward to old browser error page
	if(!Modernizr.csstransforms) { // css transforms
		window.location.replace(Config.get('errorPageOldBrowser'));
		return false;
	}


	var isInitialised, isLoaded;
	var pageObj;

	$(function(){
		var $body = $('body');
		if( $body.hasClass('world3d-body') ){
			require(['app/3dworld'], function(page){
				pageObj = page;
				page.init($body);
				isInitialised = true;
				checkLoaded();
			});
		} else if($body.hasClass('content-slideshow-body')) {
			require(['slideshow'], function(page){
				page.init($body);
				isInitialised = true;
				checkLoaded();
			});
		} else if($body.hasClass('content-film-body')) {
			require(['film'], function(page){
				page.init($body);
				isInitialised = true;
				checkLoaded();
			});
		} else if($body.hasClass('content-foldshow-body')) {
			require(['foldshow'], function(page){
				page.init($body);
				isInitialised = true;
				checkLoaded();
			});
		} else if($body.hasClass('cseries-body')) {
			require(['cseries'], function(page){
				page.init($body);
				isInitialised = true;
				checkLoaded();
			});
		}
	});

	(function(){
		var readyStateCheckInterval = setInterval(function() {
			if (document.readyState === "complete") {
				loaded();
				clearInterval(readyStateCheckInterval);
			}
		}, 100);

		function loaded() {
			isLoaded = true;
			checkLoaded();
		}
	})();

	function checkLoaded() {
		if ( isInitialised && isLoaded ) {
			$('html').removeClass('is-not-loaded').addClass('is-loaded');

			if( $('body').hasClass('world3d-body') ){
				pageObj.onPageLoaded();
			}
		}
	}
});

define("main", function(){});

