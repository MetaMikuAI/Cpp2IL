using System.Collections.Generic;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Api;

public abstract class Cpp2IlOutputFormat
{
    /// <summary>
    /// The ID of the output format as used when specifying an output format (e.g. in the command line)
    /// </summary>
    public abstract string OutputFormatId { get; }

    /// <summary>
    /// The name of the output format displayed to the user (e.g. in logs or the GUI)
    /// </summary>
    public abstract string OutputFormatName { get; }

    /// <summary>
    /// IDs of the processing layers this output format needs in order to produce complete output.
    /// Any of these the user hasn't asked for are run before the ones they have.
    /// </summary>
    public virtual IEnumerable<string> RequiredProcessingLayerIds => [];

    /// <summary>
    /// Called when this output format is selected by the user, before any binary is loaded.
    /// You do not have a context, but you could use this to, for example, configure the library if you need to enable a feature.
    /// </summary>
    public virtual void OnOutputFormatSelected()
    {
    }

    public abstract void DoOutput(ApplicationAnalysisContext context, string outputRoot);
}
