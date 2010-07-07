/*
 * Determine your JDK
 */

import java.lang.management.RuntimeMXBean;
import java.lang.management.ManagementFactory;
import java.util.Map;
import java.lang.management.OperatingSystemMXBean;
/**
 *
 * @author luecke
 */
public class java_version {

    /**
     * @param None
     */
    public static void main(String[] args) {
        RuntimeMXBean mxBean = ManagementFactory.getRuntimeMXBean();
        OperatingSystemMXBean mxOS = ManagementFactory.getOperatingSystemMXBean();
        Map<String, String> p = mxBean.getSystemProperties();
        System.out.println("Vendor:     " + mxBean.getVmVendor());
        System.out.println("VM Name:    " + mxBean.getVmName() + " " +
                mxBean.getVmVersion());
        System.out.println("Runtime:    " + p.get("java.runtime.name") + " " +
                p.get("java.runtime.version"));
        System.out.println("OS:         " + mxOS.getName() + " " + mxOS.getArch()
                + " " + mxOS.getVersion());
        System.out.println("Processors: " + mxOS.getAvailableProcessors());
    }

}
