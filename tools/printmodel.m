function r = printmodel(filename, varargin)
% printmodel(filename)
% printmodel(filename, options)
% Generate eps and log files from a Simulink model
%
% Prints a Simulink model and its simulation output to eps files. All
% subsystems are printed to files named
%   filename-sys<n>.eps
% where <n> are integers from 1.. to the number of subystems.
%
% By default, the model is also simulated, and any scope blocks are
% printed to eps files named:
%   filename-<scopename>.eps
% where <scopename> is the (all lowercase) name of the scope block.
%
% The actual values logged are printed to log files named:
%   filename-<scopename>.log
%
% The options are:
% nosim      - print the model but do not simulate i
% exit	     - exit matlab when done
% eval	     - command to evaluate before running the simulation,
%	       but after loading the model
% maxloglen  - truncate the log
% 

% Author: T.Bourke, INRIA, Feb 2011

% %%
%  Extract optional input options

simulate = 1;
exitafterward = 0;
commands = {};
maxloglen = -1;

k = 1;
while (k <= length(varargin))
    if strcmp(varargin{k}, 'nosim')
	simulate = 0;
    end

    if strcmp(varargin{k}, 'exit')
	exitafterward = 1;
    end

    if strcmp(varargin{k}, 'eval')
	if (k + 1 <= length(varargin))
	    k = k + 1;
	    commands = cat(1, commands, varargin{k});
	end
    end

    if strcmp(varargin{k}, 'maxloglen')
	if (k + 1 <= length(varargin))
	    k = k + 1;
	    maxloglen = str2num(varargin{k});
	end
    end

    k = k + 1;
end

% %%
% Print the model and subsystems

[path, name, ext] = fileparts(filename);
filename = fullfile([path name]);

sys = load_system(filename);

cellfun((@(x) fprintf('%s = %s\n', x, get_param(filename, x))), ...
	 {'SolverName', 'SolverType', 'SolverMode', 'Starttime', ...
	  'StopTime', 'MaxStep', 'MinStep', 'InitialStep', 'FixedStep', ...
	  'ZcThreshold', 'RelTol', 'AbsTol'})

PrintData.PrintLog='off';
PrintData.PrintFrame='';
PrintData.FileName=strcat(filename, '-sys');
PrintData.PrintOptions='-deps';
PrintData.PaperOrientation='landscape';
PrintData.PaperType='a4';
PrintData.PrintTsLegend=0;

simprintdlg(sys, 'AllSystems', 0, 0, PrintData);

% %%
% Simulate the model and print the output of all scopes

scopes = find_system(sys, 'BlockType', 'Scope');
names = {};
ylims = {};
for i = 1:size(scopes)
    scope = scopes(i);
    name = lower(get(scope, 'Name'));

    set(scope, 'SaveToWorkspace', 'On');
    set(scope, 'SaveName', name);

    ymin = regexp(get(scope, 'YMin'), '~', 'split');
    ymax = regexp(get(scope, 'YMax'), '~', 'split');
    ylim = str2double([ymin; ymax]);

    names = cat(1, names, name);
    ylims = cat(1, ylims, ylim);
end

if simulate
    for i = 1:length(commands)
	commands(i)
	eval(char(commands(i)));
    end;

    sout = sim(filename, 'ReturnWorkspaceOutputs', 'on');

    for i = 1:size(names)
	name = names{i};
	ylim = ylims{i};
	data = sout.find(name);

	% make the plot

	[hfig, haxes, hlines] = simplot(data);

	for i = 1:size(haxes,1)
	    % set(haxes(i), 'YLim', get(haxes(i), 'YLim') + [-0.1 0.1]);
	    set(haxes(i), 'YLim', ylim(:,i) + [-0.1; 0.1]);
	end

	set(hfig, 'PaperType', 'A4');
	set(hfig, 'PaperOrientation', 'landscape');
	print(hfig, '-deps', strcat(filename, '-', name));

	close(hfig);

	% dump the values to a log file
	logfname = strcat(filename, '-', name, '.log');

	logf = fopen(logfname, 'w');
	fprintf(logf, 't');
	for j = 1:size(data.signals, 2)
	    fprintf(logf, '\t%s', data.signals(j).label);
	end;
	fprintf(logf, '\n');
	fclose(logf);

	loglen = size(data.time, 1);
	if maxloglen > 0
	    loglen = maxloglen;
	end;

	r = [data.time data.signals.values];
	dlmwrite(logfname, r(1:loglen,:), '-append',...
		 'delimiter', '\t',...
		 'newline', 'unix',...
		 'precision', '%.15f');
    end;
end;

if exitafterward
    exit;
end;

